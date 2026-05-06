module Styles where

-- | CSS Module class name lookups.
-- | Each record field corresponds to a class name in the .module.css file.
-- | Parcel scopes the actual class names at build time.

type AppStyles =
  { root :: String
  , sidebar :: String
  , resizer :: String
  , resizerActive :: String
  , sidebarTitle :: String
  , navSectionHeader :: String
  , navItem :: String
  , navItemSelected :: String
  , statusDot :: String
  , statusMatch :: String
  , statusMismatch :: String
  , content :: String
  , contentTitle :: String
  , loading :: String
  , placeholder :: String
  }

type CircuitDiffStyles =
  { tabBar :: String
  , tab :: String
  , tabActive :: String
  , legend :: String
  , legendItem :: String
  , swatchPublicInput :: String
  , swatchDiff :: String
  , swatchPiDiff :: String
  , sideBySide :: String
  , sidePanel :: String
  , sidePanelTitle :: String
  , tableContainer :: String
  , tableBody :: String
  , tableHeader :: String
  , headerCellVar :: String
  , headerCellType :: String
  , headerCellValue :: String
  , constRow :: String
  , constRowDiff :: String
  , cell :: String
  , cellValue :: String
  , summary :: String
  }

type GateTableStyles =
  { sidePanel :: String
  , title :: String
  , scrollContainer :: String
  , tableBody :: String
  , header :: String
  , headerCell :: String
  , headerRowNum :: String
  , virtualRow :: String
  , virtualRowPublicInput :: String
  , virtualRowDiff :: String
  , virtualRowPiDiff :: String
  , virtualRowClickable :: String
  , rowContent :: String
  , rowNum :: String
  , contextIndicator :: String
  , dataCell :: String
  , contextExpanded :: String
  }

foreign import appStyles_ :: AppStyles
foreign import circuitDiffStyles_ :: CircuitDiffStyles
foreign import gateTableStyles_ :: GateTableStyles
