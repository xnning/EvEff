{-# LANGUAGE TypeOperators, FlexibleContexts, Rank2Types, MagicHash #-}
module Control.Ev.Util where

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

state :: a -> Eff (State a :* e) ans -> Eff e ans
state init 
  = handlerLocal init (State{ get = function (\_ -> localGet),
                              put = function (\x -> localSet x) })


------------
-- Write
------------

data Writer a e ans = Writer { tell :: !(Op a () e ans) }

writer :: (Monoid a) => a -> Eff (Writer a :* e) ans -> Eff e (ans,a)
writer init
  = handlerLocalRet init (,) $
    Writer{ tell = function (\x -> do{ localUpdate (\y -> mappend y x); return () }) }


------------
-- Exn
------------

data Exn e ans = Exn { throwError :: forall a. Op String a e ans }

exn :: Eff (Exn :* e) ans -> Eff e (Either String ans)
exn
  = handlerRet Right (Exn{ throwError = operation (\msg resume -> return (Left msg) ) })

defaultExn :: ans -> Eff (Exn :* e) ans -> Eff e ans
defaultExn def
  = handler (Exn{ throwError = operation (\msg resume -> return def) })

maybeExn :: Eff (Exn :* e) ans -> Eff e (Maybe ans)
maybeExn
  = handlerRet Just (Exn{ throwError = operation (\msg resume -> return Nothing) })
