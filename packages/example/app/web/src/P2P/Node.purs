-- | The per-peer gossip state machine: the decentralized job-board, now over
-- | MANY blocks. Each base prover owns its own block (its own private
-- | transactions); every block is a perfect-binary merge DAG identified by its
-- | root content-address key. Merge provers help merge ready slots of ANY
-- | block. No coordinator: peers derive each block's DAG from its public leaf
-- | statements and gossip a globally content-addressed job-board
-- | (`Have`/`Claim`/`Request`/`Deliver`); a node proved by anyone stops being
-- | counted everywhere, duplicate work is idempotent, dropped claims free on
-- | TTL, and every received proof is verified before being merged on.
-- |
-- | All gossip state is keyed by node content-address (`stmtKey`), which is
-- | globally unique across blocks — so `globalHave`/`claims`/`provers` need no
-- | block id. Proving is manual: `step` proves exactly one unit and waits.
module Snarky.Example.P2P.Node
  ( Mode(..)
  , StartConfig
  , startNode
  ) where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (for_, sum)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Set (Set)
import Data.Set as Set
import Data.String as String
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..), fst)
import Effect (Effect)
import Effect.Aff (Aff, launchAff_)
import Effect.Class (liftEffect)
import Effect.Exception (throw)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Snarky.Example.Merge (decodeStmt)
import Snarky.Example.P2P.Cache as Cache
import Snarky.Example.P2P.Dag (DagView)
import Snarky.Example.P2P.Dag as Dag
import Snarky.Example.P2P.Protocol (Msg(..), decodeMsg, encodeMsg)
import Snarky.Example.P2P.ProverClient (BlockMeta, Client)
import Snarky.Example.P2P.ProverClient as RPC
import Snarky.Example.P2P.Transport (Transport)
import Snarky.Example.P2P.Transport as T

foreign import nowMs :: Effect Number

data Mode = Base | Merge

modeStr :: Mode -> String
modeStr = case _ of
  Base -> "base"
  Merge -> "merge"

-- | A block as this peer tracks it: its public shape + derived DAG.
type Block = { meta :: BlockMeta, dag :: DagView }

type StartConfig =
  { transport :: Transport
  , client :: Client
  , mode :: Mode
  , log :: { severity :: String, text :: String } -> Effect Unit
  , onScan ::
      { blocks :: Array { blockId :: String, n :: Int, statuses :: Array { slot :: Int, status :: String, by :: String } }
      , steppable :: Int
      }
      -> Effect Unit
  }

type St =
  { cfg :: StartConfig
  , myId :: String
  , fingerprint :: Ref String
  , blocks :: Ref (Map String Block) -- blockId (root key) -> block
  , myBlock :: Ref (Maybe String) -- base mode: the block this peer generated
  , haveWire :: Ref (Map String String) -- node key -> proof wire (local)
  , globalHave :: Ref (Set String) -- node keys known to exist anywhere
  , claims :: Ref (Map String { peerId :: String, ts :: Number }) -- node key -> claim
  , provers :: Ref (Map String String) -- node key -> producing peer
  , requested :: Ref (Set String) -- keys we've already asked for
  , busy :: Ref Boolean
  , doneBlocks :: Ref (Set String) -- blocks whose root has verified
  }

claimTtlMs :: Number
claimTtlMs = 30000.0

startNode :: StartConfig -> Effect { step :: Effect Unit }
startNode cfg = do
  fp <- Ref.new ""
  blocks <- Ref.new Map.empty
  myBlock <- Ref.new Nothing
  haveWire <- Ref.new Map.empty
  globalHave <- Ref.new Set.empty
  claims <- Ref.new Map.empty
  provers <- Ref.new Map.empty
  requested <- Ref.new Set.empty
  busy <- Ref.new false
  doneBlocks <- Ref.new Set.empty
  let
    st =
      { cfg
      , myId: T.myId cfg.transport
      , fingerprint: fp
      , blocks
      , myBlock
      , haveWire
      , globalHave
      , claims
      , provers
      , requested
      , busy
      , doneBlocks
      }
  T.onMessage cfg.transport (handleRaw st)
  T.onPeer cfg.transport \peer -> do
    cfg.log { severity: "info", text: "peer connected: " <> peer }
    greet st peer
  launchAff_ do
    cached <- Cache.cacheAll
    liftEffect $ for_ cached \c -> do
      Ref.modify_ (Map.insert c.key c.wire) st.haveWire
      Ref.modify_ (Set.insert c.key) st.globalHave
    when (not (Array.null cached)) $ liftEffect $
      cfg.log { severity: "info", text: "restored " <> show (Array.length cached) <> " cached proofs" }
    fingerprint <- RPC.initService cfg.client
    liftEffect do
      Ref.write fingerprint st.fingerprint
      cfg.log { severity: "info", text: "compiled; fingerprint " <> fingerprint }
    case cfg.mode of
      Base -> startBase st
      Merge -> liftEffect do
        helloAll st
        onState st
  pure { step: step st }

log_ :: St -> String -> String -> Effect Unit
log_ st sev text = st.cfg.log { severity: sev, text }

localKeys :: St -> Effect (Array String)
localKeys st = do
  pairs <- Map.toUnfoldable <$> Ref.read st.haveWire :: Effect (Array (Tuple String String))
  pure (map fst pairs)

proverOf :: St -> String -> Effect String
proverOf st key = (fromMaybe st.myId <<< Map.lookup key) <$> Ref.read st.provers

recordProver :: St -> String -> String -> Effect Unit
recordProver st key by =
  Ref.modify_ (\mp -> if Map.member key mp then mp else Map.insert key by mp) st.provers

-- | Broadcast our presence + the proof keys we hold.
helloAll :: St -> Effect Unit
helloAll st = do
  keys <- localKeys st
  fp <- Ref.read st.fingerprint
  T.broadcast st.cfg.transport (encodeMsg (Hello { peerId: st.myId, role: modeStr st.cfg.mode, fingerprint: fp, haveKeys: keys }))

-- | Greet a newly-connected peer: Hello + every block we know + our Haves.
greet :: St -> String -> Effect Unit
greet st peer = do
  fp <- Ref.read st.fingerprint
  keys <- localKeys st
  T.sendTo st.cfg.transport peer (encodeMsg (Hello { peerId: st.myId, role: modeStr st.cfg.mode, fingerprint: fp, haveKeys: keys }))
  bs <- Ref.read st.blocks
  for_ (Map.values bs) \b -> T.sendTo st.cfg.transport peer (encodeMsg (BlockAnnounce b.meta))
  for_ keys \k -> do
    by <- proverOf st k
    T.sendTo st.cfg.transport peer (encodeMsg (Have { key: k, by }))

-- | Build a DAG from a block's leaf statements and register it (idempotent by
-- | block id = root key). Returns the block id and whether it was new.
addBlock :: St -> BlockMeta -> Effect { blockId :: String, isNew :: Boolean }
addBlock st meta = do
  let sorted = Array.sortWith _.slot meta.leafStmts
  stmts <- traverse
    ( \r -> case decodeStmt r.stmt of
        Right s -> pure s
        Left e -> throw ("bad leaf stmt: " <> show e)
    )
    sorted
  let dag = Dag.buildDag meta.n stmts
  let blockId = Dag.rootKey dag
  existing <- Map.member blockId <$> Ref.read st.blocks
  when (not existing) do
    Ref.modify_ (Map.insert blockId { meta, dag }) st.blocks
    announceLocalHaves st
  pure { blockId, isNew: not existing }

-- | BASE mode: generate THIS peer's own block, register + announce it, and prove
-- | its base proofs on demand (`step`). Each base prover owns one block; many
-- | base provers in a session means many blocks proved in parallel.
startBase :: St -> Aff Unit
startBase st = do
  meta <- RPC.genBlock st.cfg.client
  liftEffect do
    res <- addBlock st meta
    Ref.write (Just res.blockId) st.myBlock
    log_ st "info" ("generated block " <> shortId res.blockId <> ": " <> show meta.n <> " transactions — click “prove next” to prove each base proof")
    T.broadcast st.cfg.transport (encodeMsg (BlockAnnounce meta))
    onState st

-- | A short, readable fingerprint of a block id (the id is a JSON statement
-- | `{"source":"<digits>","target":…}`; show a slice of the source digits).
shortId :: String -> String
shortId s = String.take 8 (String.drop 11 s)

storeProof :: St -> String -> String -> Effect Unit
storeProof st key wire = do
  Ref.modify_ (Map.insert key wire) st.haveWire
  Ref.modify_ (Set.insert key) st.globalHave
  Cache.cachePut key wire
  reportScan st

-- | Announce a `Have` for every local proof (covers cache-restored proofs).
announceLocalHaves :: St -> Effect Unit
announceLocalHaves st = do
  keys <- localKeys st
  for_ keys \k -> do
    by <- proverOf st k
    T.broadcast st.cfg.transport (encodeMsg (Have { key: k, by }))

reportScan :: St -> Effect Unit
reportScan st = do
  bs <- Ref.read st.blocks
  gh <- Ref.read st.globalHave
  provers <- Ref.read st.provers
  steppable <- steppableCount st bs gh
  let
    blockViews = map
      ( \(Tuple bid b) ->
          { blockId: bid
          , n: b.dag.n
          , statuses: map
              ( \slot ->
                  { slot
                  , status: statusOf b.dag gh slot
                  , by: fromMaybe "" (Map.lookup (Dag.keyOf b.dag slot) provers)
                  }
              )
              (Array.range 1 (2 * b.dag.n - 1))
          }
      )
      (Map.toUnfoldable bs :: Array (Tuple String Block))
  st.cfg.onScan { blocks: blockViews, steppable }

-- | Nodes of this peer's role still needing proof, NETWORK-WIDE (off globalHave,
-- | so every peer agrees). Base: this peer's own block's unproved leaves. Merge:
-- | ready merge slots summed across all blocks.
steppableCount :: St -> Map String Block -> Set String -> Effect Int
steppableCount st bs gh = case st.cfg.mode of
  Base -> do
    mb <- Ref.read st.myBlock
    pure case mb >>= \bid -> Map.lookup bid bs of
      Just b -> Array.length $ Array.filter (\j -> not (Set.member (Dag.keyOf b.dag (b.dag.n + j)) gh)) (Array.range 0 (b.dag.n - 1))
      Nothing -> 0
  Merge -> pure $ sum (map (\b -> Array.length (Dag.ready b.dag gh)) (Array.fromFoldable (Map.values bs)))

-- | May we take node `key`? Yes unless a peer with a lower id holds a fresh claim.
mayTake :: St -> Map String { peerId :: String, ts :: Number } -> Number -> String -> Boolean
mayTake st cls now key = case Map.lookup key cls of
  Just c -> c.peerId >= st.myId || (now - c.ts) > claimTtlMs
  Nothing -> true

statusOf :: DagView -> Set String -> Int -> String
statusOf d gh slot
  | Set.member (Dag.keyOf d slot) gh = "complete"
  | slot >= d.n = "pending"
  | Set.member (Dag.keyOf d (2 * slot)) gh && Set.member (Dag.keyOf d (2 * slot + 1)) gh = "pending"
  | otherwise = "locked"

-- | Incoming raw message. (No peer cap in the app — the test suite bounds peers.)
handleRaw :: St -> String -> String -> Effect Unit
handleRaw st from raw = case decodeMsg raw of
  Left _ -> pure unit
  Right msg -> handle st from msg

handle :: St -> String -> Msg -> Effect Unit
handle st from = case _ of
  Hello h -> do
    log_ st "info" ("peer " <> h.peerId <> " is a " <> h.role <> " prover")
    fp <- Ref.read st.fingerprint
    when (fp /= "" && h.fingerprint /= "" && fp /= h.fingerprint) do
      log_ st "warning" ("peer " <> h.peerId <> " has a different build fingerprint — ignoring (reload to the same version)")
    when (fp == "" || h.fingerprint == "" || fp == h.fingerprint) do
      Ref.modify_ (Set.union (Set.fromFoldable h.haveKeys)) st.globalHave
      bs <- Ref.read st.blocks
      for_ (Map.values bs) \b -> T.sendTo st.cfg.transport from (encodeMsg (BlockAnnounce b.meta))
      onState st
  BlockAnnounce meta -> do
    res <- addBlock st meta
    when res.isNew $ log_ st "info" ("learned block " <> shortId res.blockId <> ": " <> show meta.n <> " leaves")
    onState st
  Have hv -> do
    Ref.modify_ (Set.insert hv.key) st.globalHave
    recordProver st hv.key hv.by
    onState st
  Claim c -> do
    Ref.modify_ (Map.insert c.key { peerId: c.peerId, ts: c.ts }) st.claims
    onState st
  Request r -> do
    have <- Ref.read st.haveWire
    case Map.lookup r.key have of
      Just wire -> T.sendTo st.cfg.transport from (encodeMsg (Deliver { key: r.key, wire }))
      Nothing -> pure unit
  Deliver d -> do
    storeProof st d.key d.wire
    Ref.modify_ (Set.delete d.key) st.requested
    onState st

-- | React to a state change: refresh the view, prune completed claims, fetch the
-- | children of ready slots (merge mode), and verify each block's root once it
-- | appears. Never proves.
onState :: St -> Effect Unit
onState st = do
  bs <- Ref.read st.blocks
  gh <- Ref.read st.globalHave
  -- drop claims for nodes now complete network-wide
  Ref.modify_ (Map.filterWithKey (\key _ -> not (Set.member key gh))) st.claims
  for_ (Map.toUnfoldable bs :: Array (Tuple String Block)) \(Tuple bid b) -> do
    case st.cfg.mode of
      Merge -> for_ (Dag.ready b.dag gh) \s -> do
        requestIfNeeded st (Dag.keyOf b.dag (2 * s))
        requestIfNeeded st (Dag.keyOf b.dag (2 * s + 1))
      Base -> pure unit
    when (Set.member (Dag.rootKey b.dag) gh) (finishRoot st bid b.dag)
  reportScan st

-- | Prove exactly ONE unit, then stop. Base: the next unproved leaf of this
-- | peer's block. Merge: the lowest ready merge slot across all blocks.
step :: St -> Effect Unit
step st = do
  busy <- Ref.read st.busy
  if busy then log_ st "info" "still proving — wait for the current proof to finish"
  else case st.cfg.mode of
    Base -> stepBase st
    Merge -> stepMerge st

stepBase :: St -> Effect Unit
stepBase st = do
  mb <- Ref.read st.myBlock
  bs <- Ref.read st.blocks
  gh <- Ref.read st.globalHave
  case mb >>= \bid -> Map.lookup bid bs of
    Nothing -> log_ st "info" "no block yet — still generating"
    Just b -> do
      let unproved = Array.filter (\j -> not (Set.member (Dag.keyOf b.dag (b.dag.n + j)) gh)) (Array.range 0 (b.dag.n - 1))
      case Array.head unproved of
        Nothing -> log_ st "info" "all base proofs done — merge peers take it from here"
        Just j -> do
          Ref.write true st.busy
          log_ st "info" ("proving base proof for tx " <> show j <> "…")
          launchAff_ do
            leaf <- RPC.proveBaseLeaf st.cfg.client j
            liftEffect do
              Ref.write false st.busy
              recordProver st leaf.key st.myId
              storeProof st leaf.key leaf.wire
              T.broadcast st.cfg.transport (encodeMsg (Have { key: leaf.key, by: st.myId }))
              log_ st "info" ("proved base proof for tx " <> show j)
              onState st

type Cand = { dag :: DagView, slot :: Int, key :: String, aKey :: String, bKey :: String }

stepMerge :: St -> Effect Unit
stepMerge st = do
  bs <- Ref.read st.blocks
  gh <- Ref.read st.globalHave
  cls <- Ref.read st.claims
  now <- nowMs
  have <- Ref.read st.haveWire
  let
    cands :: Array Cand
    cands = Array.filter (\c -> mayTake st cls now c.key) $
      Array.concatMap
        ( \b -> map
            ( \s ->
                { dag: b.dag
                , slot: s
                , key: Dag.keyOf b.dag s
                , aKey: Dag.keyOf b.dag (2 * s)
                , bKey: Dag.keyOf b.dag (2 * s + 1)
                }
            )
            (Dag.ready b.dag gh)
        )
        (Array.fromFoldable (Map.values bs))
  case Array.head cands of
    Nothing -> log_ st "info" "no merge ready yet — waiting for child proofs to be published"
    Just c -> case Map.lookup c.aKey have, Map.lookup c.bKey have of
      Just aWire, Just bWire -> mergeNode st c aWire bWire
      _, _ -> do
        requestIfNeeded st c.aKey
        requestIfNeeded st c.bKey
        log_ st "info" ("fetching inputs for a merge — click “prove next” again once they arrive")

mergeNode :: St -> Cand -> String -> String -> Effect Unit
mergeNode st c aWire bWire = do
  now <- nowMs
  T.broadcast st.cfg.transport (encodeMsg (Claim { key: c.key, peerId: st.myId, ts: now }))
  Ref.write true st.busy
  log_ st "info" ("merging slot " <> show c.slot <> "…")
  launchAff_ do
    out <- RPC.merge st.cfg.client { aWire, bWire }
    liftEffect do
      Ref.write false st.busy
      if out.wire == "" then
        log_ st "error" ("merge slot " <> show c.slot <> " rejected (child verify failed)")
      else do
        recordProver st out.key st.myId
        storeProof st out.key out.wire
        T.broadcast st.cfg.transport (encodeMsg (Have { key: out.key, by: st.myId }))
        log_ st "info" ("merged slot " <> show c.slot)
      onState st

requestIfNeeded :: St -> String -> Effect Unit
requestIfNeeded st key = do
  have <- Ref.read st.haveWire
  req <- Ref.read st.requested
  when (not (Map.member key have) && not (Set.member key req)) do
    Ref.modify_ (Set.insert key) st.requested
    T.broadcast st.cfg.transport (encodeMsg (Request { key }))

finishRoot :: St -> String -> DagView -> Effect Unit
finishRoot st bid dag = do
  done <- Ref.read st.doneBlocks
  when (not (Set.member bid done)) do
    have <- Ref.read st.haveWire
    case Map.lookup (Dag.rootKey dag) have of
      Just rootWire -> do
        Ref.modify_ (Set.insert bid) st.doneBlocks
        launchAff_ do
          ok <- RPC.verify st.cfg.client rootWire
          liftEffect $ log_ st (if ok then "info" else "error")
            (if ok then "block " <> shortId bid <> " root proof verified — accepted ✓" else "block " <> shortId bid <> " root verification FAILED")
      Nothing -> requestIfNeeded st (Dag.rootKey dag)
