{-# LANGUAGE TypeOperators, FlexibleContexts, Rank2Types, MagicHash #-}
module Control.Ev.Util
  ( Reader(Reader,ask)
  , reader, lreader
  , State(State,get,put)
  , state, lstate
  , Writer(Writer,tell)
  , writer, lwriter
  , Exn(Exn,throwError)
  , exn, defaultExn, maybeExn
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

{-# INLINE lreader #-}
lreader :: a -> Eff (Linear (Reader a) :* e) ans -> Eff e ans
lreader x
  = handler (Linear (Reader{ ask = lvalue x }))

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

{-# INLINE lstate #-}
lstate :: a -> Eff (Linear (State a) :* e) ans -> Eff e ans
lstate init
  = handlerLocal init (Linear (State{ get = lfunction (\_ -> localGet),
                                      put = lfunction (\x -> localPut x) }))


------------
-- Write
------------

data Writer a e ans = Writer { tell :: !(Op a () e ans) }

{-# INLINE writer #-}
writer :: (Monoid a) => Eff (Writer a :* e) ans -> Eff e (ans,a)
writer
  = handlerLocalRet [] (\x xs -> (x,mconcat (reverse xs))) $
    Writer{ tell = function (\x -> do{ localUpdate (\xs -> x:xs); return () }) }

{-# INLINE lwriter #-}
lwriter :: (Monoid a) => Eff (Linear (Writer a) :* e) ans -> Eff e (ans,a)
lwriter
  = handlerLocalRet [] (\x xs -> (x,mconcat (reverse xs))) $
    Linear (Writer{ tell = lfunction (\x -> do{ localUpdate (\xs -> x:xs); return () }) })

------------
-- Exn
------------

data Exn e ans = Exn { throwError :: forall a. Op String a e ans }

exn :: Eff (Exn :* e) ans -> Eff e (Either String ans)
exn
  = handlerRet Right (Exn{ throwError = except (\msg -> return (Left msg) ) })

defaultExn :: ans -> Eff (Exn :* e) ans -> Eff e ans
defaultExn def
  = handler (Exn{ throwError = except (\msg -> return def) })

maybeExn :: Eff (Exn :* e) ans -> Eff e (Maybe ans)
maybeExn
  = handlerRet Just (Exn{ throwError = except (\msg -> return Nothing) })
