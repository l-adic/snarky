module Test.Snarky.Example.Config where

import Mina.ChainId (ChainId(..))

chainId :: ChainId
chainId = Testnet

-- | Tree depth for this test.
type Depth = 4