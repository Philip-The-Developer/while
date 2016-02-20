{-|
  Module      : Interface.Pos
  Description : Defines position type to be used for source code locations.
  Copyright   : 2014, Jonas Cleve
  License     : GPL-3
-}
module Interface.Pos (
  -- * Data types
  SourcePos (..),

  -- * Helper functions
  initialPosition, nextLine, nextColumn, incrColumn
) where

import Prelude (
    String, Int,
    Show, Eq,
    (+), (++),
    show
  )

-- | Defines the position inside a source code.
data SourcePos
  = SourcePos {
    sourceName :: String,   -- ^ The name – usually the file name.
    sourceLine :: Int,      -- ^ The line of the source.
    sourceColumn :: Int     -- ^ The column in the current line.
  }
  deriving (Eq)

-- | Display the Position as @(\<file\>,\<line\>,\<column\>)@.
instance Show SourcePos where
  show (SourcePos name line column) = "(" ++ name ++ "," ++ show line ++ "," ++
                                      show column ++ ")"

-- | Start at the beginning of a source with given name.
initialPosition :: String -> SourcePos
initialPosition name = SourcePos
  { sourceName = name
  , sourceLine = 1
  , sourceColumn = 1
  }

-- | Move the position to the next line.
nextLine :: SourcePos -> SourcePos
nextLine p = p { sourceLine = 1 + sourceLine p, sourceColumn = 1 }

-- | Increments the column counter by one.
nextColumn :: SourcePos -> SourcePos
nextColumn p = p { sourceColumn = 1 + sourceColumn p }

-- | Increments the column counter by the given value.
incrColumn :: SourcePos -> Int -> SourcePos
incrColumn p i = p { sourceColumn = i + sourceColumn p }
