{-|
  Module      : Parser.Functional.Library
  Description : Functional parser library.
  Copyright   : 2014, Jonas Cleve
                2015, Tay Phuong Ho
  License     : GPL-3
-}
module Parser.Functional.Library (
  Parser (..),
  next, eof, chainl1, mzero, return, mplus,
  (<|>), (>>=)
) where

import Prelude (
    Monad (..),
    Maybe (..)
  )
import Control.Applicative (
    Alternative(..), Applicative(..)
  )
import Data.Functor(Functor(..))
import Control.Monad (
    MonadPlus (..), liftM, ap
  )

-- * Functional parser library

-- ** Basic definition

-- | Create new parser type with @s@ being the input stream and @r@ being the
--   result the parser generates.
newtype Parser s r = Parser { runParser :: s -> Maybe (r, s) }

{-# ANN module "HLint: ignore Use const" #-}
-- | Let the parser be an instance of the monad to ease creating and joining
--   together parsers.
instance Monad (Parser s) where
  -- | This is a parser which does not use its input and returns what is given
  return r = Parser (\s -> Just (r, s))
  -- | Chaining two parsers together is running the first one and then the
  --   second on the output of the first if it was successful.
  p >>= f = Parser (\s -> case runParser p s of
                            Just (r, s') -> runParser (f r) s'
                            Nothing      -> Nothing)

instance Functor (Parser s) where -- § added
    fmap = liftM

instance Applicative (Parser s) where -- § added
    pure  = return
    (<*>) = ap

-- | Being an instance of the plus monad gives support for choice and failure.
instance MonadPlus (Parser s) where
  -- | Failure: a parser that always fails.
  mzero = Parser (\_ -> Nothing)
  -- | Choice: Return the result of the first parser if successful, else the
  --   result of the second parser.
  p1 `mplus` p2 = Parser (\s -> case runParser p1 s of
                                  Nothing -> runParser p2 s
                                  r       -> r)

instance Alternative (Parser s) where -- § added
  (<|>) = mplus
  empty = mzero

-- ** Combinators

-- | Chains a parser @p@ in a left associative way separated by parser @op@
--   which returns the combining function.
chainl1 :: Parser s r -> Parser s (r -> r -> r) -> Parser s r
p `chainl1` op = p >>= rest
  where
    rest x = (do
        f <- op
        y <- p
        rest (f x y)
      ) <|> return x

-- -- | Matches the given parser @p@ any number of times (including 0) making it
-- --   @p*@.
-- many :: Parser s r -> Parser s [r]
-- many p = many1 p <|> return []

-- -- | Matches the given parser @p@ any number of times (at least once) making it
-- --   @p+@. This effectively runs @p@ and then @'many' p@.
-- many1 :: Parser s r -> Parser s [r]
-- many1 p = do
--   x <- p
--   xs <- many p
--   return (x:xs)

-- ** Basic parsers

-- | Matches the first element from the input stream.
next :: Parser [r] r
next = Parser (
    \s -> case s of
      []     -> Nothing
      t:rest -> Just (t, rest)
  )

-- | Matches only the end of file. Fails otherwise.
eof :: Parser [se] ()
eof = Parser (\s -> case s of
                      [] -> Just ((), s)
                      _  -> Nothing)
