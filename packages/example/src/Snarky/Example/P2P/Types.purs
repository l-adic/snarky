-- | The P2P star's domain newtypes. These exist so the wire-level strings the
-- | star shuffles around can't be confused with one another (a peer id is not a
-- | job id is not an encoded payload). `Show` renders the bare string, so they
-- | interpolate into logs cleanly.
module Snarky.Example.P2P.Types
  ( PeerId(..)
  , JobId(..)
  , Payload(..)
  , Frame(..)
  ) where

import Prelude

import Data.Newtype (class Newtype)

-- | A peer/node identity within a transport room.
newtype PeerId = PeerId String

derive instance Newtype PeerId _
derive newtype instance Eq PeerId
derive newtype instance Ord PeerId

instance Show PeerId where
  show (PeerId s) = s

-- | A coordinator-assigned correlation id pairing an `Assign` with its
-- | `Result`/`Reject`. Independent of the snark manager's slot id.
newtype JobId = JobId String

derive instance Newtype JobId _
derive newtype instance Eq JobId
derive newtype instance Ord JobId

instance Show JobId where
  show (JobId s) = s

-- | An encoded work item or proof — the opaque payload the star is generic over
-- | (`prove`, `Assign.work`, `Result.proof`). Typed callers encode/decode it at
-- | the edges; the star never inspects it.
newtype Payload = Payload String

derive instance Newtype Payload _
derive newtype instance Eq Payload

instance Show Payload where
  show (Payload s) = s

-- | An encoded protocol message as it travels over a `Transport`.
newtype Frame = Frame String

derive instance Newtype Frame _
derive newtype instance Eq Frame

instance Show Frame where
  show (Frame s) = s
