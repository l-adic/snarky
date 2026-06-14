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

-- | Middle-ellipsis truncation for long opaque identifiers (addresses,
-- | hashes): keeps the prefix AND suffix, both of which matter for
-- | recognizing a `B62…` key. The full value stays available on hover.
shortenMid :: String -> String
shortenMid s
  | String.length s <= 24 = s
  | otherwise = String.take 10 s <> "…" <> String.drop (String.length s - 8) s

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
      [ idField "hash" tx.hash
      , field "nonce" tx.nonce
      , idField "from" tx.from
      , idField "to" tx.to
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
  -- Long opaque identifiers: show middle-truncated, full value on hover.
  idField label value = R.div
    { className: "tx-field"
    , children:
        [ R.span { className: "tx-field-label", children: [ R.text label ] }
        , R.span
            { className: "tx-field-value mono"
            , title: value
            , children: [ R.text (shortenMid value) ]
            }
        ]
    }
