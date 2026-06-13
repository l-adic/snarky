-- | Shared panel primitives used by the section components. Styling is
-- | in web/styles.css (`.panel`, `.panel-title`, `.empty`).
module Snarky.Example.Web.Component.Panel
  ( panel
  , emptyHint
  ) where

import Prelude

import React.Basic (JSX)
import React.Basic.DOM as R

-- | A titled panel: an uppercase header row over its body.
panel :: String -> Array JSX -> JSX
panel title children = R.div
  { className: "panel"
  , children: [ R.div { className: "panel-title", children: [ R.text title ] } ] <> children
  }

-- | The placeholder shown in a panel with no content yet.
emptyHint :: JSX
emptyHint = R.span { className: "empty", children: [ R.text "—" ] }
