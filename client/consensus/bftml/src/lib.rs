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
    traits::{
		Block as BlockT, Header as HeaderT, Hash as HashT,
		DigestItemFor, ProvideRuntimeApi, Zero,
    },
    Justification, ConsensusEngineId,
};
use sp_consensus::{
    self, BlockImport, Environment, Proposer, BlockCheckParams, ForkChoiceStrategy,
    BlockImportParams, BlockOrigin, ImportResult, Error as ConsensusError,
    SelectChain, SyncOracle, CanAuthorWith,
    import_queue::{Verifier, BasicQueue, CacheKeyId},
};
use sc_client_api::{
    backend::{AuxStore, Backend},
    call_executor::CallExecutor,
    BlockchainEvents, ProvideUncles,
};
use sc_keystore::KeyStorePtr;
use sc_client::Client;
use sp_block_builder::BlockBuilder as BlockBuilderApi;
use sp_blockchain::{
    Result as ClientResult, Error as ClientError, HeaderBackend,
    ProvideCache, HeaderMetadata,
    well_known_cache_keys::{self, Id as CacheKeyId},
};
use sp_api::ApiExt;
use sc_network_gossip::{Validator, ValidationResult, TopicNotification};

mod _app {
    use sp_application_crypto::{
	app_crypto, sr25519, key_types::BFTML,
    };
    app_crypto!(sr25519, BFTML);
}

#[cfg(feature = "std")]
pub type AuthorityPair = _app::Pair;
pub type AuthoritySignature = _app::Signature;
pub type AuthorityId = _app::Public;
pub const BFTML_ENGINE_ID: ConsensusEngineId = *b"BFTML";


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




type BlockProposal = BlockImportParams;


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
    imported_block_rx: UnboundedReceiver<BlockProposal>,
    // substrate to consensus engine channel tx
    tc_tx: UnboundedSender<Vec<u8>>,
    // consensus engine to substrate channel rx
    ts_rx: UnboundedReceiver<Vec<u8>>,
    // commit block channel rx
    cb_rx: UnboundedReceiver<CommitBlockMsg>,
    // import block channel tx
    ib_tx: UnboundedSender<BlockProposal>,
    // ask proposal channel tx
    ap_tx: UnboundedSender<String>,
    // give proposal channel tx
    gp_tx: UnboundedSender<String>,

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
	imported_block_rx: UnboundedReceiver<BlockProposal>,
	tc_tx: UnboundedSender<Vec<u8>>,
	ts_rx: UnboundedReceiver<Vec<u8>>,
	cb_rx: UnboundedReceiver<CommitBlockMsg>,
	ib_tx: UnboundedSender<BlockProposal>,
	ap_rx: UnboundedReceiver<String>,
	gp_tx: UnboundedSender<BlockProposal>
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
	    cb_rx,
	    ib_tx,
	    ap_rx,
	    gp_tx,
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

    fn commit_block() {
	// finish commiting block

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
	// receive ask proposal directive
	match self.ap_rx.poll()? {
	    Async::Ready(Some(msg)) => {
		// mint a new block on current local node
		self.mint_block(authority_index);
	    },
	    _ => {}
	}

	// imported block
	match self.imported_block_rx.poll()? {
	    Async::Ready(Some(block)) => {
		// stuff to do, do we need to wrap this struct BlockImportParams to a new type?
		// send this block to consensus engine
		self.ib_tx.unbounded_send(block);
		self.gp_tx.unbounded_send(block);
	    },
	    _ => {}
	}

	// gossip communication
	// get msg from gossip network
	match self.gossip_incoming_end.poll()? {
	    Async::Ready(Some(msg)) => {
		// here, msg type is TopicNotification
		let message = msg.message.clone();

		// send it to consensus engine
		self.tc_tx.unbounded_send(message);
	    },
	    _ => {}
	}

	// get msg from consensus engine
	match self.ts_rx.poll()? {
	    Async::Ready(Some(msg)) => {
		let topic = make_topic();
		self.gossip_engine.gossip_message(topic, msg, false);
	    },
	    _ => {}
	}

	match self.cb_rx.poll()? {
	    Async::Ready(Some(commit_block_msg)) => {
		// mint a new block on current local node
		self.commit_block(commit_block_msg);
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
pub struct BftmlVerifier<B, E, Block: BlockT, RA> {
    client: Arc<Client<B, E, Block, RA>>,
}

impl<B, E, Block, RA> Verifier<Block> for BftmlVerifier<B, E, Block, RA> where
    B: Backend<Block, Blake2Hasher> + 'static,
    E: CallExecutor<Block, Blake2Hasher> + 'static + Clone + Send + Sync,
    Block: BlockT<Hash=H256>,
    RA: Send + Sync,
{
    fn verify(
	&mut self,
	origin: BlockOrigin,
	header: Block::Header,
	justification: Option<Justification>,
	mut body: Option<Vec<Block::Extrinsic>>,
    ) -> Result<(BlockImportParams<Block>, Option<Vec<(CacheKeyId, Vec<u8>)>>), String> {

	let pre_digest = find_pre_digest::<Block>(&header)?;

	let v_params = VerificationParams {
	    header: header.clone(),
	    pre_digest: Some(pre_digest.clone()),
	};

	let checked_result = check_header::<Block>(v_params)?;
	match checked_result {
	    CheckedHeader::Checked(pre_header, verified_info) => {
		let block_import_params = BlockImportParams {
		    origin,
		    header: pre_header,
		    post_digests: vec![verified_info.seal],
		    body,
		    // TODO: need set true? for instant finalization
		    finalized: false,
		    justification,
		    auxiliary: Vec::new(),
		    fork_choice: ForkChoiceStrategy::LongestChain,
		    allow_missing_state: false,
		    import_existing: false,
		};

		Ok((block_import_params, Default::default()))
	    },
	    CheckedHeader::NotChecked => {
		Err("Verify failed!")
	    }
	}
    }
}



pub struct BftmlBlockImport<B, E, Block: BlockT, RA, I> {
    client: Arc<Client<B, E, Block, RA>>,
    inner_block_import: I,
    imported_block_tx: UnboundedSender<BlockImportParams>
}

impl<B, E, Block: BlockT, RA, I> Clone for BftmlBlockImport<B, E, Block, RA, I> {
    fn clone(&self) -> Self {
	RhdBlockImport {
	    client: self.client.clone(),
	    inner_block_import: self.inner_block_import.clone(),
	    imported_block_tx: self.imported_block_tx.clone()
	}
    }
}

impl<B, E, Block: BlockT, RA, I> BftmlBlockImport<B, E, Block, RA, I> {
    fn new(
	client: Arc<Client<B, E, Block, RA>>,
	block_import: I,
	imported_block_tx: UnboundedSender<BlockImportParams>
    ) -> Self {
	BftmlBlockImport {
	    client,
	    inner_block_import: block_import,
	    imported_block_tx
	}
    }
}

impl<B, E, Block, RA, I> BlockImport<Block> for BftmlBlockImport<B, E, Block, RA, I> where
    B: Backend<Block, Blake2Hasher> + 'static,
    E: CallExecutor<Block, Blake2Hasher> + 'static + Clone + Send + Sync,
    Block: BlockT<Hash=H256>,
    RA: Send + Sync,
    I: BlockImport<Block> + Send + Sync,
    I::Error: Into<ConsensusError>,
{
    type Error = ConsensusError;

    fn check_block(
	&mut self,
	block: BlockCheckParams<Block>,
    ) -> Result<ImportResult, Self::Error> {
	self.inner.check_block(block)
	    //.map_err(Into::into)
    }

    fn import_block(
	&mut self,
	mut block: BlockImportParams<Block>,
	new_cache: HashMap<CacheKeyId, Vec<u8>>,
    ) -> Result<ImportResult, Self::Error> {

	let hash = block.post_header().hash();
	let number = block.header.number().clone();

	// early exit if block already in chain, otherwise the check for
	// epoch changes will error when trying to re-import an epoch change
	match self.client.status(BlockId::Hash(hash)) {
	    Ok(sp_blockchain::BlockStatus::InChain) => return Ok(ImportResult::AlreadyInChain),
	    Ok(sp_blockchain::BlockStatus::Unknown) => {},
	    Err(e) => return Err(ConsensusError::ClientImport(e.to_string())),
	}

	let pre_digest = find_pre_digest::<Block>(&block.header)
	    .expect("valid bftml headers must contain a predigest; \
		     header has been already verified; qed");
	let parent_hash = *block.header.parent_hash();
	let parent_header = self.client.header(&BlockId::Hash(parent_hash))
	    .map_err(|e| ConsensusError::ChainLookup(e.to_string()))?
	    .ok_or_else(|| ConsensusError::ChainLookup(babe_err(
		Error::<Block>::ParentUnavailable(parent_hash, hash)
	    ).into()))?;


	let import_result = self.inner_block_import.import_block(block.clone(), new_cache);

	// send block to channel
	self.imported_block_tx.unbounded_send(block);

	import_result.map_err(Into::into)
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
	UnboundedSender<Vec<u8>>,
	UnboundedReceiver<Vec<u8>>,
	UnboundedSender<Vec<u8>>,
	UnboundedReceiver<Vec<u8>>
    ){

	// Consensus engine to substrate consensus msg channel
	let (ts_tx, ts_rx) = mpsc::unbounded();

	// Substrate to consensus engine consensus msg channel
	let (tc_tx, tc_rx) = mpsc::unbounded();

	(tc_tx, tc_rx, ts_tx, ts_rx)
    }

    pub fn gen_ask_proposal_channel() -> (UnboundedSender<String>, UnboundedReceiver<String>) {
	let (ap_tx, ap_rx) = mpsc::unbounded();

	(ap_tx, ap_rx)
    }

    pub fn gen_give_proposal_channel() -> (UnboundedSender<BlockProposal>, UnboundedReceiver<BlockProposal>) {
	let (gp_tx, gp_rx) = mpsc::unbounded();

	(gp_tx, gp_rx)
    }


    pub fn gen_commit_block_channel() -> (UnboundedSender<CommitBlockMsg>, UnboundedReceiver<CommitBlockMsg>) {
	let (cb_tx, cb_rx) = mpsc::unbounded();

	(cb_tx, cb_rx)
    }

    pub fn gen_import_block_channel() -> (UnboundedSender<BlockProposal>, UnboundedReceiver<BlockProposal>) {
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
