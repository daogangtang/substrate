use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::{self, Instant, Duration};
use futures::prelude::*;
use futures::future;
use futures::sync::oneshot;
use tokio::runtime::TaskExecutor;
use tokio::timer::Delay;
use parking_lot::{RwLock, Mutex};

use codec::{Encode, Decode, Codec};
use sp_core::{Blake2Hasher, H256, Pair};
use sp_runtime::{
    generic::{BlockId, OpaqueDigestItemId},
    traits::{Block, Header, Hash, DigestItemFor, Zero},
    Justification, ConsensusEngineId,
};
use sp_consensus::{
    self, BlockImport, Environment, Proposer, BlockCheckParams, ForkChoiceStrategy,
    BlockImportParams, BlockOrigin, ImportResult, Error as ConsensusError,
    SelectChain, SyncOracle, CanAuthorWith,
    import_queue::{Verifier, BasicQueue, CacheKeyId},
};
use sp_block_builder::BlockBuilder as BlockBuilderApi;
use sp_blockchain::{
    Result as ClientResult, Error as ClientError, HeaderBackend,
    ProvideCache, HeaderMetadata,
    well_known_cache_keys::{self, Id as CacheKeyId},
};
use sp_api::{ApiExt, ProvideRuntimeApi};
use sp_timestamp::{InherentError, TimestampInherentData};
use sc_client_api::{
    backend::{AuxStore, Backend},
    call_executor::CallExecutor,
    BlockchainEvents, ProvideUncles,
};
use sc_keystore::KeyStorePtr;
//[XXX] Client has been removed by default, add it as a generic parameter
use sc_client::Client;
use sc_network_gossip::{Validator, ValidationResult, TopicNotification};

mod _app {
    use sp_application_crypto::{
        //[XXX]: BFTML was added into sp_core::crypto::key_types;
        app_crypto, sr25519, key_types::BFTML,
    };
    app_crypto!(sr25519, BFTML);
}

#[cfg(feature = "std")]
pub type AuthorityPair = _app::Pair;
pub type AuthoritySignature = _app::Signature;
pub type AuthorityId = _app::Public;
// ConsensusEngineId type is: [u8; 4];
pub const BFTML_ENGINE_ID: ConsensusEngineId = b"BFTE";


struct BftmlPreDigest {
    authority_index: u32
}


#[derive(derive_more::Display, Debug)]
enum Error<B: BlockT> {
        #[display(fmt = "Multiple BABE pre-runtime digests, rejecting!")]
        MultiplePreRuntimeDigests,
        #[display(fmt = "No BABE pre-runtime digest found")]
        NoPreRuntimeDigest,
        #[display(fmt = "Multiple BABE epoch change digests, rejecting!")]
        MultipleEpochChangeDigests,
        #[display(fmt = "Parent ({}) of {} unavailable. Cannot import", _0, _1)]
        ParentUnavailable(B::Hash, B::Hash),
        #[display(fmt = "Header {:?} has a bad seal", _0)]
        HeaderBadSeal(B::Hash),
        #[display(fmt = "Header {:?} is unsealed", _0)]
        HeaderUnsealed(B::Hash),
        #[display(fmt = "Bad signature on {:?}", _0)]
        BadSignature(B::Hash),
        #[display(fmt = "Invalid author: Expected secondary author: {:?}, got: {:?}.", _0, _1)]
        InvalidAuthor(AuthorityId, AuthorityId),
        #[display(fmt = "Could not fetch parent header: {:?}", _0)]
        FetchParentHeader(sp_blockchain::Error),
        #[display(fmt = "Block {} is not valid under any epoch.", _0)]
        BlockNotValid(B::Hash),
        #[display(fmt = "Parent block of {} has no associated weight", _0)]
        ParentBlockNoAssociatedWeight(B::Hash),
        #[display(fmt = "Checking inherents failed: {}", _0)]
        CheckInherents(String),
        Client(sp_blockchain::Error),
        Runtime(sp_inherents::Error),
}

// Bft consensus middle layer channel messages
pub enum BftmlChannelMsg {
    // block msg varaints
    // u32, authority_index
    MintBlock(u32),
    // contains the block passed through
    ImportBlock(BlockImportParams),
    // gossip msg varaints
    // the inner data is raw opaque u8 vector, parsed by high level consensus engine
    GossipMsgIncoming(Vec<u8>),
    GossipMsgOutgoing(Vec<u8>),
}


//
// Core bft consensus middle layer worker
//
pub struct BftmlWorker<B, I, E> {
    // hold a ref to substrate client
    client: Arc<Client>,
    // hold a ref to substrate block import instance
    block_import: Arc<Mutex<I>>,
    // proposer for new block
    proposer_factory: E,
    // instance of the gossip network engine
    gossip_engine: GossipEngine<B>,
    // gossip network message incoming channel
    gossip_incoming_end: UnboundedReceiver<TopicNotification>,
    // imported block channel rx, from block import handle
    imported_block_rx: UnboundedReceiver<BlockImportParams>,
    // substrate to consensus engine channel tx
    tc_tx: UnboundedSender<BftmlChannelMsg>,
    // consensus engine to substrate channel rx
    ts_rx: UnboundedReceiver<BftmlChannelMsg>,
    // mint block channel rx
    mb_rx: UnboundedReceiver<BftmlChannelMsg>,
    // import block channel tx
    ib_tx: UnboundedSender<BftmlChannelMsg>

}


impl<B, I, E> BftmlWorker<B, I, E> where
    B: BlockT + Clone + Eq,
    B::Hash: ::std::hash::Hash,
    I: BlockImport<B>,
    E: Environment<B> + Send + Sync
{
    pub fn new(
        client: Arc<Client>,
        block_import: Arc<Mutex<I>>,
        proposer_factory: E,
        imported_block_rx: UnboundedReceiver<BlockImportParams>,
        tc_tx: UnboundedSender<BftmlChannelMsg>,
        ts_rx: UnboundedReceiver<BftmlChannelMsg>,
        mb_rx: UnboundedReceiver<BftmlChannelMsg>,
        ib_tx: UnboundedSender<BftmlChannelMsg>
    ) {

        let gossip_engine = crate::gen::gen_gossip_engine();
        let topic = make_topic();
        let gossip_incoming_end = crate::gen::gen_gossip_incoming_end(&gossip_engine, topic);

        BftmlWorker {
            client,
            block_import,
            proposer_factory,
            gossip_engine,
            gossip_incoming_end,
            imported_block_rx,
            tc_tx,
            ts_rx,
            mb_rx,
            ib_tx,
        }
    }

    fn proposer(&mut self, block: &B::Header) -> Result<E::Proposer, sp_consensus::Error> {
        self.proposer_factory.init(block).map_err(|e| {
            sp_consensus::Error::ClientImport(format!("{:?}", e))
        })
    }

    fn mint_block(&mut self, authority_index: u32) {
        let chain_head = match self.client.best_chain() {
            Ok(x) => x,
            Err(e) => {
                // TODO:
                return;
            }
        };

        // TODO: error handling
        let proposer = self.proposer(&chain_head).unwrap();

        // assign emplty values now
        let inherent_data = InherentData::new();
        // TODO: could emply value be ok?
        let digests = sp_runtime::generic::Digest {
            logs: Vec::new()
        };
        let duration = time::Duration::seconds(12);

        // make a proposal
        let proposing = proposer.propose(inherent_data, digests, duration)
            .map_err(|e| sp_consensus::Error::ClientImport(format!("{:?}", e)));;


        proposing.map_ok(move |block| {
            let (header, body) = block.deconstruct();
            let header_num = *header.number();
            let header_hash = header.hash();
            let parent_hash = *header.parent_hash();

            // pub authorities: Vec<(AuthorityId, BabeAuthorityWeight)>,
            // how to get myself authority_id
            let authority_id: AuthorityId = ...;

            // sign the pre-sealed hash of the block and then
            // add it to a digest item.
            let signature = authority_id.sign(header_hash.as_ref());
            let signature_digest_item = <DigestItemFor<B> as CompatibleDigestItem>::bftml_seal(signature);

            let block_import_params = BlockImportParams {
                origin: BlockOrigin::Own,
                header,
                justification: None,
                post_digests: vec![signature_digest_item],
                body: Some(body),
                finalized: false,
                auxiliary: Vec::new(), // block-weight is written in block import.
                // TODO: block-import handles fork choice and this shouldn't even have the
                // option to specify one.
                // https://github.com/paritytech/substrate/issues/3623
                fork_choice: ForkChoiceStrategy::LongestChain,
                allow_missing_state: false,
                import_existing: false,
            };

            info!("Pre-sealed block for proposal at {}. Hash now {:?}, previously {:?}.",
                  header_num,
                  block_import_params.post_header().hash(),
                  header_hash,
            );

            // immediately import this block
            if let Err(err) = block_import.lock().import_block(block_import_params, Default::default()) {
                // warn!(target: "bftml",
                //	  "Error with block built on {:?}: {:?}",
                //	  parent_hash,
                //	  err,
                // );
            }
        })
        // TODO: need to check, for futures01
            .map(|_| future::ready(Ok()));

        // Here, we'd better use block mode to finish this block minting.
        proposing.wait();
    }
}


impl<B, I, E> Future for BftmlWorker<B, I, E> where
    B: BlockT + Clone + Eq,
    B::Hash: ::std::hash::Hash,
    I: BlockImport<B>,
    E: Environment<B> + Send + Sync
{
    // Here, We need to three thing
    // 1. poll the making block directive channel rx to make a new block;
    // 2. on imported a full block, send this new block to new block channel tx;
    // 3. poll the gossip engine consensus message channel rx, send message to gossip network;
    //    and on received a new consensus message from gossip network, send it to another consensus message channel tx;
    type Item = ();
    type Error = io::Error;

    fn poll(&mut self) -> Poll<(), Self::Error> {
        // receive mint block directive
        match self.mb_rx.poll()? {
            Async::Ready(Some(msg)) => {
                if let BftmlChannelMsg::MintBlock(authority_index) = msg {
                    // mint block
                    self.mint_block(authority_index);
                }
            },
            _ => {}
        }

        // impoted block
        match self.imported_block_rx.poll()? {
            Async::Ready(Some(block)) => {
                // stuff to do, do we need to wrap this struct BlockImportParams to a new type?
                // send this block to consensus engine
                self.ib_tx.unbounded_send(BftmlChannelMsg::ImportBlock(block));
            },
            _ => {}
        }

        // gossip communication
        // get msg from gossip network
        match self.gossip_incoming_end.poll()? {
            Async::Ready(Some(msg)) => {
                // here, msg type is TopicNotification
                let message = msg.message.clone();
                let msg_to_send = BftmlChannelMsg::GossipMsgIncoming(message);

                // send it to consensus engine
                self.tc_tx.unbounded_send(msg_to_send);
            },
            _ => {}
        }

        // get msg from consensus engine
        match self.ts_rx.poll()? {
            Async::Ready(Some(msg)) => {
                match msg {
                    BftmlChannelMsg::GossipMsgOutgoing(message) => {
                        // send it to gossip network
                        let topic = make_topic();
                        self.gossip_engine.gossip_message(topic, message, false);
                    },
                    _ => {}
                }
            },
            _ => {}
        }

        Ok(Async::NotReady)
    }

}



// /// Create a unique topic for a round and set-id combo.
// pub fn round_topic<B: BlockT>(round: RoundNumber, set_id: SetIdNumber) -> B::Hash {
//     <<B::Header as HeaderT>::Hashing as HashT>::hash(format!("{}-{}", set_id, round).as_bytes())
// }

pub fn make_topic<B: BlockT>() -> B::Hash {
    <<B::Header as HeaderT>::Hashing as HashT>::hash(format!("topic-{}", "bftmlgossip").as_bytes())
}


/// Validator is needed by a gossip engine instance
/// A validator for Bftml gossip messages.
pub(super) struct GossipValidator<Block: BlockT> {
}

impl<Block> GossipValidator<Block> {
    pub fn new() {
        GossipValidator
    }
}

/// Implemention of the network_gossip::Validator
/// We copy the default implemention from the definition of Validator
/// And we need only implemente method validate() here.
impl<Block: BlockT> sc_network_gossip::Validator<Block> for GossipValidator<Block> {
    /// New peer is connected.
    fn new_peer(&self, _context: &mut dyn ValidatorContext<B>, _who: &PeerId, _roles: Roles) {
    }

    /// New connection is dropped.
    fn peer_disconnected(&self, _context: &mut dyn ValidatorContext<B>, _who: &PeerId) {
    }

    /// Validate consensus message.
    fn validate(
        &self,
        context: &mut dyn ValidatorContext<B>,
        sender: &PeerId,
        data: &[u8]
    ) -> ValidationResult<B::Hash> {
        // now, we should create a topic for message
        // XXX: we'd better to create unique topic for each round
        // but now, we can create a fixed topic to test.
        let topic = make_topic();

        // And we return ProcessAndKeep variant to test
        sc_network_gossip::ValidationResult::ProcessAndKeep(topic)
    }

    /// Produce a closure for validating messages on a given topic.
    fn message_expired<'a>(&'a self) -> Box<dyn FnMut(B::Hash, &[u8]) -> bool + 'a> {
        Box::new(move |_topic, _data| false)
    }

    /// Produce a closure for filtering egress messages.
    fn message_allowed<'a>(&'a self) -> Box<dyn FnMut(&PeerId, MessageIntent, &B::Hash, &[u8]) -> bool + 'a> {
        Box::new(move |_who, _intent, _topic, _data| true)
    }

}



//
// Stuff must be implmented: Verifier, BlockImport, ImportQueue
//
pub struct BftmlVerifier<B: Block> {
	_marker: PhantomData<B>,
}

impl<B: Block> BftmlVerifier<B> {
	pub fn new() -> Self {
		Self { _marker: PhantomData }
	}

	fn check_header(
		&self,
		mut header: B::Header,
	) -> Result<(B::Header, DigestItem<B::Hash>), Error<B>>	{
		let hash = header.hash();

		let (seal, inner_seal) = match header.digest_mut().pop() {
			Some(DigestItem::Seal(id, seal)) => {
				if id == BFTML_ENGINE_ID{
					(DigestItem::Seal(id, seal.clone()), seal)
				} else {
					return Err(Error::WrongEngine(id))
				}
			},
			_ => return Err(Error::HeaderUnsealed(hash)),
		};

		let _pre_hash = header.hash();
        // TODO: check pre_hash

		Ok((header, seal))
	}
}

impl<B: Block> Verifier<B> for BftmlVerifier<B> {
    fn verify(
        &mut self,
        origin: BlockOrigin,
        header: Block::Header,
        justification: Option<Justification>,
        mut body: Option<Vec<Block::Extrinsic>>,
    ) -> Result<(BlockImportParams<B, ()>, Option<Vec<(CacheKeyId, Vec<u8>)>>), String> {
		let hash = header.hash();
		let (checked_header, seal) = self.check_header(header)?;

		let mut import_block = BlockImportParams::new(origin, checked_header);
		import_block.post_digests.push(seal);
		import_block.body = body;
		import_block.justification = justification;
		import_block.post_hash = Some(hash);

		Ok((import_block, None))
    }
}


pub struct BftmlBlockImport<B: Block, C, I, S> {
    client: Arc<C>,
    inner: I,
    select_chain: Option<S>,
    inherent_data_providers: sp_inherents::InherentDataProviders,
    check_inherents_after: <<B as Block>::Header as Header>::Number,
    imported_block_tx: UnboundedSender<BlockImportParams>,
}

impl<B: Block, C, I, S> Clone for BftmlBlockImport<B, C, I, S> {
    fn clone(&self) -> Self {
        BftmlBlockImport {
            client: self.client.clone(),
            inner: self.inner.clone(),
            select_chain: self.select_chain.clone(),
            inherent_data_providers: self.inherent_data_providers.clone(),
            check_inherents_after: self.check_inherents_after.clone(),
            imported_block_tx: self.imported_block_tx.clone()
        }
    }
}

impl<B, C, I, S> BftmlBlockImport<B, C, I, S>
where
    B: Block,
    C: ProvideRuntimeApi<B> + Send + Sync + HeaderBackend<B> + AuxStore + ProvideCache<B> + BlockOf,
    C::Api: BlockBuilderApi<B, Error = sp_blockchain::Error>,
    I: BlockImport<B, Transaction = sp_api::TransactionFor<C, B>> + Send + Sync,
    I::Error: Into<ConsensusError>,
{
    pub fn new(
        client: Arc<C>,
        inner: I,
        select_chain: Option<S>,
        inherent_data_providers: sp_inherents::InherentDataProviders,
        check_inherents_after: <<B as BlockT>::Header as HeaderT>::Number,
        imported_block_tx: UnboundedSender<BlockImportParams>,
    ) -> Self {
        BftmlBlockImport {
            client,
            inner,
            select_chain,
            inherent_data_providers,
            check_inherents_after,
            imported_block_tx,
        }
    }

	fn check_inherents(
		&self,
		block: B,
		inherent_data: InherentData,
		timestamp_now: u64,
	) -> Result<(), Error<B>> {
		const MAX_TIMESTAMP_DRIFT_SECS: u64 = 60;

		if *block.header().number() < self.check_inherents_after {
			return Ok(())
		}

		let inherent_res = self.client.runtime_api().check_inherents(
			block,
			inherent_data,
		).map_err(Error::Client)?;

		if !inherent_res.ok() {
			inherent_res
				.into_errors()
				.try_for_each(|(i, e)| match InherentError::try_from(&i, &e) {
					Some(InherentError::ValidAtTimestamp(timestamp)) => {
						if timestamp > timestamp_now + MAX_TIMESTAMP_DRIFT_SECS {
							return Err(Error::TooFarInFuture);
						}

						Ok(())
					},
					Some(InherentError::Other(e)) => Err(Error::Runtime(e)),
					None => Err(Error::CheckInherents(
						self.inherent_data_providers.error_to_string(&i, &e)
					)),
				})
		} else {
			Ok(())
		}
	}
}

impl<B, C, I, S> BlockImport<B> for BftmlBlockImport<B, C, I, S>
where
    B: Block,
    C: ProvideRuntimeApi<B> + Send + Sync + HeaderBackend<B> + AuxStore + ProvideCache<B> + BlockOf,
    C::Api: BlockBuilderApi<B, Error = sp_blockchain::Error>,
    I: BlockImport<B, Transaction = sp_api::TransactionFor<C, B>> + Send + Sync,
    I::Error: Into<ConsensusError>,
	S: SelectChain<B>,
{
	type Error = ConsensusError;
	type Transaction = sp_api::TransactionFor<C, B>;

    fn check_block(
        &mut self,
        block: BlockCheckParams<B>,
    ) -> Result<ImportResult, Self::Error> {
        self.inner.check_block(block).map_err(Into::into)
    }

    fn import_block(
        &mut self,
        mut block: BlockImportParams<B, Self::Transaction>,
        new_cache: HashMap<CacheKeyId, Vec<u8>>,
    ) -> Result<ImportResult, Self::Error> {

		let best_hash = match self.select_chain.as_ref() {
			Some(select_chain) => select_chain.best_chain()
				.map_err(|e| format!("Fetch best chain failed via select chain: {:?}", e))?
				.hash(),
			None => self.client.info().best_hash,
		};

		if let Some(inner_body) = block.body.take() {
			let inherent_data = self.inherent_data_providers
				.create_inherent_data().map_err(|e| e.into_string())?;
			let timestamp_now = inherent_data.timestamp_inherent_data().map_err(|e| e.into_string())?;

			let check_block = B::new(block.header.clone(), inner_body);

			self.check_inherents(
				check_block.clone(),
				inherent_data,
				timestamp_now
			)?;

			block.body = Some(check_block.deconstruct().1);
		}

		let _inner_seal = match block.post_digests.last() {
			Some(DigestItem::Seal(id, seal)) => {
				if id == &BFTML_ENGINE_ID {
					seal.clone()
				} else {
					return Err(Error::<B>::WrongEngine(*id).into())
				}
			},
			_ => return Err(Error::<B>::HeaderUnsealed(block.header.hash()).into()),
		};

        // TODO: verify inner_seal

		if block.fork_choice.is_none() {
			block.fork_choice = Some(ForkChoiceStrategy::Custom(true));
		}

        // send imported block to upper channel
        self.imported_block_tx.unbounded_send(block.clone());

		self.inner.import_block(block, new_cache).map_err(Into::into)
    }
}

pub type ImportedBlockLink = mpsc::UnboundedReceiver<BlockImportParams>;

pub fn gen_block_import_handle<B, E, Block: BlockT<Hash=H256>, RA, I>(
    client: Arc<Client<B, E, Block, RA>>,
) -> ClientResult<(RhdBlockImport<B, E, Block, RA, I>, ImportedBlockLink)> where
    B: Backend<Block, Blake2Hasher>,
    E: CallExecutor<Block, Blake2Hasher> + Send + Sync,
    RA: Send + Sync,
    I: BlockImport<Block> + Send + Sync,
    I::Error: Into<ConsensusError>,
{

    let default_block_import = client.clone();

    let (imported_block_tx, imported_block_rx) = crate::gen::gen_imported_block_link();

    let import_handle = BftmlBlockImport::new(
        client: client.clone(),
        inner_block_import: default_block_import,
        imported_block_tx
    );

    Ok((import_handle, imported_block_rx))
}



/// The Bftml import queue type.
pub type BftmlImportQueue<B> = BasicQueue<B>;

pub fn gen_import_queue<B, E, Block: BlockT<Hash=H256>, RA, I>(
    client: Arc<Client<B, E, Block, RA>>,
    block_import: I,
) -> ClientResult<BftmlImportQueue<Block>> where
    B: Backend<Block, Blake2Hasher> + 'static,
    E: CallExecutor<Block, Blake2Hasher> + Clone + Send + Sync + 'static,
    RA: Send + Sync + 'static,
    I: BlockImport<Block,Error=ConsensusError> + Send + Sync + 'static,
{

    let verifier = BftmlVerifier {
        client: client.clone(),
    };

    let justification_import = None;
    let finality_proof_import = None;

    Ok(BasicQueue::new(
        verifier,
        Box::new(block_import),
        justification_import,
        finality_proof_import,
    ))
}


//
// Helper Function
//
fn get_authorities<A, B, C>(client: &C, at: &BlockId<B>) -> Result<Vec<A>, ConsensusError> where
    A: Codec,
    B: BlockT,
    C: ProvideRuntimeApi + BlockOf + ProvideCache<B>,
{
    client
        .cache()
        .and_then(|cache| cache
                  .get_at(&well_known_cache_keys::AUTHORITIES, at)
                  .and_then(|(_, _, v)| Decode::decode(&mut &v[..]).ok())
        )
        .ok_or_else(|| sp_consensus::Error::InvalidAuthoritiesSet.into())
}


pub enum CheckedHeader<H, S> {
    Checked(H, S),
    NotChecked
}

struct VerificationParams<B: BlockT> {
    pub header: B::Header,
    pub pre_digest: Option<BftmlPreDigest>,
}

struct VerifiedHeaderInfo<B: BlockT> {
    pub pre_digest: DigestItemFor<B>,
    pub seal: DigestItemFor<B>,
    pub author: AuthorityId,
}

fn check_header<B: BlockT + Sized>(
    params: VerificationParams<B>,
) -> Result<CheckedHeader<B::Header, VerifiedHeaderInfo<B>>, Error<B>> where
    DigestItemFor<B>: CompatibleDigestItem,
{
    let VerificationParams {
        mut header,
        pre_digest,
    } = params;

    //let hash = header.hash();
    let parent_hash = *header.parent_hash();
    let authorities = get_authorities(self.client.as_ref(), &BlockId::Hash(parent_hash))
        .map_err(|e| format!("Could not fetch authorities at {:?}: {:?}", parent_hash, e))?;

    let author = match authorities.get(pre_digest.authority_index() as usize) {
        Some(author) => author.0.clone(),
        None => return Err(Error::SlotAuthorNotFound),
    };

    let seal = match header.digest_mut().pop() {
        Some(x) => x,
        None => return Err(Error::HeaderUnsealed(header.hash())),
    };

    let info = VerifiedHeaderInfo {
        pre_digest: CompatibleDigestItem::bftml_pre_digest(pre_digest),
        seal,
        author,
    };
    Ok(CheckedHeader::Checked(header, info))
}

fn find_pre_digest<B: BlockT>(header: &B::Header) -> Result<BftmlPreDigest, Error<B>>
{
    // genesis block doesn't contain a pre digest so let's generate a
    // dummy one to not break any invariants in the rest of the code
    if header.number().is_zero() {
        return Ok(BftmlPreDigest {
            authority_index: 0,
        });
    }

    let mut pre_digest: Option<_> = None;
    for log in header.digest().logs() {
        trace!(target: "bftml", "Checking log {:?}, looking for pre runtime digest", log);
        match (log.as_bftml_pre_digest(), pre_digest.is_some()) {
            (Some(_), true) => return Err(Error::MultiplePreRuntimeDigests),
            (None, _) => trace!(target: "bftml", "Ignoring digest not meant for us"),
            (s, false) => pre_digest = s,
        }
    }
    pre_digest.ok_or_else(|| Error::NoPreRuntimeDigest)
}

/// A digest item which is usable with Bftml consensus.
#[cfg(feature = "std")]
pub trait CompatibleDigestItem: Sized {
        fn bftml_pre_digest(seal: BftmlPreDigest) -> Self;
        fn as_bftml_pre_digest(&self) -> Option<BftmlPreDigest>;
        fn bftml_seal(signature: AuthoritySignature) -> Self;
        // fn as_bftml_seal(&self) -> Option<AuthoritySignature>;
}

#[cfg(feature = "std")]
impl<Hash> CompatibleDigestItem for DigestItem<Hash> where
    Hash: Debug + Send + Sync + Eq + Clone + Codec + 'static
{
    fn bftml_pre_digest(digest: BftmlPreDigest) -> Self {
        DigestItem::PreRuntime(BFTML_ENGINE_ID, digest.encode())
    }

    fn as_bftml_pre_digest(&self) -> Option<BftmlPreDigest> {
        self.try_to(OpaqueDigestItemId::PreRuntime(&BFTML_ENGINE_ID))
    }

    fn bftml_seal(signature: AuthoritySignature) -> Self {
        DigestItem::Seal(BFTML_ENGINE_ID, signature.encode())
    }

    // fn as_bftml_seal(&self) -> Option<AuthoritySignature> {
    //	self.try_to(OpaqueDigestItemId::Seal(&BFTML_ENGINE_ID))
    // }

}




//
// gen module, including all generating methods about
//
pub mod gen {

    pub fn gen_consensus_msg_channels() -> (
        UnboundedSender<BftmlChannelMsg>,
        UnboundedReceiver<BftmlChannelMsg>,
        UnboundedSender<BftmlChannelMsg>,
        UnboundedReceiver<BftmlChannelMsg>
    ){

        // Consensus engine to substrate consensus msg channel
        let (ts_tx, ts_rx) = mpsc::unbounded();

        // Substrate to consensus engine consensus msg channel
        let (tc_tx, tc_rx) = mpsc::unbounded();

        (tc_tx, tc_rx, ts_tx, ts_rx)
    }

    pub fn gen_mint_block_channel() -> (UnboundedSender<BftmlChannelMsg>, UnboundedReceiver<BftmlChannelMsg>) {
        let (mb_tx, mb_rx) = mpsc::unbounded();

        (mb_tx, mb_rx)
    }

    pub fn gen_import_block_channel() -> (UnboundedSender<BftmlChannelMsg>, UnboundedReceiver<BftmlChannelMsg>) {
        let (ib_tx, ib_rx) = mpsc::unbounded();

        (ib_tx, ib_rx)
    }

    pub fn gen_imported_block_link() -> (UnboundedSender<BlockImportParams>, UnboundedReceiver<BlockImportParams>) {
        let (imported_block_tx, imported_block_rx) = mpsc::unbounded();

        (imported_block_tx, imported_block_rx)
    }


    // pub fn gen_proposer_factory(client: Arc<Client>, ) -> ProposerFactory {
    //	let proposer_factory = sc_basic_authority::ProposerFactory {
    //	    client: service.client(),
    //	    transaction_pool: service.transaction_pool(),
    //	};

    //	proposer_factory
    // }

    pub fn<B, S, H> gen_gossip_engine(
        network: Arc<NetworkService<B, S, H>>,
        executor: &impl futures03::task::Spawn,)
        where B: BlockT,
              S: sc_network::specialization::NetworkSpecialization<B>,
              H: sc_network::ExHashT,

    {
        // `network` comes from outer, generated by the global substrate service instance
        // service.network()
        // `network` must implement gossip_network::Network<B>, and this work has been done
        // in client/network-gossip/src/lib.rs
        // so we can use it directly

        // executor is a future runtime executor
        // we use the outer service to generate this executor: service.spawn_task_handle(),
        // in bin/node/cli/src/service.rs we will get the global service of substrate (protocol)
        // let executor = ..;

        let validator = GossipValidator::new();
        let validator = Arc::new(validator);

        let gossip_engine = GossipEngine::new(network.clone(), executor, BFTML_ENGINE_ID, validator.clone());

        gossip_engine
    }

    pub fn<B> gen_gossip_incoming_end(&gossip_engine: GossipEngine<B>, topic: B::Hash) -> mpsc::UnboundedReceiver<TopicNotification> {
        let gossip_incoming_end = gossip_engine.messages_for(topic);

        // We shall put these biz to upper level consensus engine implementation
        // .map(|item| Ok::<_, ()>(item))
            // .filter_map(|notification| {
            //	let decoded = GossipMessage::<B>::decode(&mut &notification.message[..]);
            //	if let Err(ref e) = decoded {
            //	    debug!(target: "afg", "Skipping malformed message {:?}: {}", notification, e);
            //	}
            //	decoded.ok()
            // })
            // .and_then(move |msg| {
            //	match msg {
            //	    GossipMessage::Vote(msg) => {
            //	    }
            //	    _ => {
            //		debug!(target: "afg", "Skipping unknown message type");
            //		return Ok(None);
            //	    }
            //	}
            // })
            // .filter_map(|x| x)
            // .map_err(|()| Error::Network(format!("Failed to receive message on unbounded stream")));

        gossip_incoming_end
    }


}
