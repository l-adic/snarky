-- | The "block transactions" panel: an accordion of the block's
-- | transfers. Each row shows only the tx hash; clicking a row expands
-- | it (one at a time) to reveal the full transfer. Selection state is
-- | owned by Main and threaded in via props.
module Snarky.Example.Web.Component.Transactions
  ( TransactionsProps
  , transactionsPanel
  ) where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..))
import Data.String as String
import Effect (Effect)
import React.Basic (JSX)
import React.Basic.DOM as R
import React.Basic.Events (handler_)
import Snarky.Example.Web.Component.Panel (emptyHint, panel)
import Snarky.Example.Web.Engine (TxView)

type TransactionsProps =
  { txs :: Array TxView
  , selected :: Maybe Int
  -- | Toggle the row at this index (Main closes it if already open).
  , onSelect :: Int -> Effect Unit
  }

transactionsPanel :: TransactionsProps -> JSX
transactionsPanel { txs, selected, onSelect } =
  panel "block transactions" $
    if Array.null txs then [ emptyHint ]
    else Array.mapWithIndex (\i tx -> txRow (selected == Just i) (onSelect i) tx) txs

shorten :: String -> String
shorten s = if String.length s <= 18 then s else String.take 18 s <> "…"

txRow :: Boolean -> Effect Unit -> TxView -> JSX
txRow open toggle tx = R.div
  { className: "tx-item" <> (if open then " open" else "")
  , children:
      [ R.div
          { className: "tx-head"
          , onClick: handler_ toggle
          , children:
              [ R.span { className: "tx-caret", children: [ R.text (if open then "▾" else "▸") ] }
              , R.span { className: "tx-hash", children: [ R.text (shorten tx.hash) ] }
              ]
          }
      ] <> (if open then [ txDetail tx ] else [])
  }

txDetail :: TxView -> JSX
txDetail tx = R.div
  { className: "tx-detail"
  , children:
      [ field "hash" tx.hash
      , field "nonce" tx.nonce
      , field "from" tx.from
      , field "to" tx.to
      , field "amount" tx.amount
      ]
  }
  where
  field label value = R.div
    { className: "tx-field"
    , children:
        [ R.span { className: "tx-field-label", children: [ R.text label ] }
        , R.span { className: "tx-field-value", children: [ R.text value ] }
        ]
    }
