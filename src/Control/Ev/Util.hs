-------------------------------------------------------------------
-- Copyright 2020, Microsoft Research, Daan Leijen, Ningning Xie.
-- This is free software, see the LICENSE file at the root of the
-- distribution for details.
-------------------------------------------------------------------
{-# LANGUAGE TypeOperators, FlexibleContexts, Rank2Types, MagicHash #-}
module Control.Ev.Util
  ( Reader(Reader,ask)
  , reader
  , State(State,get,put)
  , state
  , Writer(Writer,tell)
  , writer
  , Except(Except,throwError)
  , catchError, exceptEither, exceptMaybe, exceptDefault
) where

import Control.Ev.Eff

------------
-- Reader
------------

data Reader a e ans = Reader { ask :: !(Op () a e ans) }

{-# INLINE reader #-}
reader :: a -> Eff (Reader a :* e) ans -> Eff e ans
reader x
  = handler (Reader{ ask = value x })

------------
-- State
------------

data State a e ans = State { get :: !(Op () a e ans)
                           , put :: !(Op a () e ans)  }

{-# INLINE state #-}
state :: a -> Eff (State a :* e) ans -> Eff e ans
state init
  = handlerLocal init (State{ get = function (\_ -> localGet),
                              put = function (\x -> localPut x) })


------------
-- Writer
------------

data Writer a e ans = Writer { tell :: !(Op a () e ans) }

{-# INLINE writer #-}
writer :: (Monoid a) => Eff (Writer a :* e) ans -> Eff e (ans,a)
writer
  = handlerLocalRet [] (\x xs -> (x,mconcat (reverse xs))) $
    Writer{ tell = function (\x -> do{ localUpdate (\xs -> x:xs); return () }) }


------------
-- Except
------------

data Except a e ans = Except { throwError :: forall b. Op a b e ans }

catchError :: Eff (Except a :* e) ans -> (a -> Eff e ans) -> Eff e ans
catchError action h
  = handler (Except{ throwError = except (\x -> h x) }) action

exceptEither :: Eff (Except a :* e) ans -> Eff e (Either a ans)
exceptEither
  = handlerRet Right (Except{ throwError = except (\x -> return (Left x) ) })

exceptDefault :: ans -> Eff (Except a :* e) ans -> Eff e ans
exceptDefault def
  = handler (Except{ throwError = except (\_ -> return def) })

exceptMaybe :: Eff (Except a :* e) ans -> Eff e (Maybe ans)
exceptMaybe
  = handlerRet Just (Except{ throwError = except (\_ -> return Nothing) })
