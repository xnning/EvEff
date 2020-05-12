{-|
Description : Definitions for some common effects.
Copyright   : (c) 2020, Microsoft Research; Daan Leijen; Ningning Xie
License     : MIT
Maintainer  : xnning@hku.hk; daan@microsoft.com
Stability   : Experimental

Some definitions for common effects.
-}
{-# LANGUAGE TypeOperators, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, UndecidableInstances, Rank2Types #-}
module Control.Ev.Util
  (
    -- * Reader
    Reader(Reader,ask)
  , reader
    -- * State
  , State(State,get,put)
  , state
    -- * Writer
  , Writer(Writer,tell)
  , writer
    -- * Exception
  , Except(Except,throwError)
  , catchError, exceptEither, exceptMaybe, exceptDefault
    -- * Choice
  , Choose(Choose,none,choose)
  , chooseFirst, chooseAll
) where

import Control.Ev.Eff
import Control.Monad
import Control.Applicative

------------
-- Reader
------------

-- | A standard reader effect for values of type @a@.
data Reader a e ans = Reader { ask :: !(Op () a e ans)  -- ^ get the reader value of type @a@ (as @`perform` ask ()@)
                             }

-- | A handler for a `Reader` effect with a value of type @a@.
{-# INLINE reader #-}
reader :: a -> Eff (Reader a :* e) ans -> Eff e ans
reader x
  = handler (Reader{ ask = value x })

{-
-- does not work due to the functional dependency in MonadReader
instance (Reader a :? e) => MR.MonadReader a (Eff e) where
  ask       = perform ask ()
-}

------------
-- State
------------

-- | A standard state effect of type @a@.
data State a e ans = State { get :: !(Op () a e ans) -- ^ Get the current state (as @`perform` get ()@)
                           , put :: !(Op a () e ans) -- ^ Set the current state (as @`perform` put x@)
                           }

-- | A state handler that takes an initial state of type @a@.
{-# INLINE state #-}
state :: a -> Eff (State a :* e) ans -> Eff e ans
state init
  = handlerLocal init (State{ get = function (\_ -> localGet),
                              put = function (\x -> localPut x) })


{-
-- does not work due to the functional dependency in MonadState
instance (State a :? e) => MS.MonadState a (Eff e) where
  get   = perform get ()
  put x = perform put x
-}

------------
-- Writer
------------

-- | A standard writer effect of type @a@
data Writer a e ans = Writer { tell :: !(Op a () e ans) -- ^ Output a value of type @a@ (as @`perform` tell msg@)
                             }

-- | A standard `Writer` handler for any monoidal type @a@. Returns the final
-- result of type @ans@ and the appended @tell@ arguments.
{-# INLINE writer #-}
writer :: (Monoid a) => Eff (Writer a :* e) ans -> Eff e (ans,a)
writer
  = handlerLocalRet [] (\x xs -> (x,mconcat (reverse xs))) $
    Writer{ tell = function (\x -> do{ xs <- localGet; localPut (x:xs); return () }) }


------------
-- Except
------------

-- | A standard exception effect, throwing values of type @a@.
data Except a e ans = Except { throwError :: !(forall b. Op a b e ans) -- ^ Throw an exception with a value of type @a@ (as @`perform` throwError x@)
                             }

-- | Handle an exception.
catchError :: Eff (Except a :* e) ans -> (a -> Eff e ans) -> Eff e ans
catchError action h
  = handler (Except{ throwError = except (\x -> h x) }) action

-- | Transform an exception effect to an @Either@ type.
exceptEither :: Eff (Except a :* e) ans -> Eff e (Either a ans)
exceptEither
  = handlerRet Right (Except{ throwError = except (\x -> return (Left x) ) })

-- | Remove the exception effect using a default value in case an exception was thrown.
exceptDefault :: ans -> Eff (Except a :* e) ans -> Eff e ans
exceptDefault def
  = handler (Except{ throwError = except (\_ -> return def) })

-- | Transform an exception effect to a @Maybe@ type.
exceptMaybe :: Eff (Except a :* e) ans -> Eff e (Maybe ans)
exceptMaybe
  = handlerRet Just (Except{ throwError = except (\_ -> return Nothing) })


--------------------------------------------------------------------------------
-- Choose
--------------------------------------------------------------------------------

-- | Choose implements backtracking.
data Choose e ans = Choose { none   :: !(forall a. Op () a e ans)  -- ^ @`perform none ()` indicates no result
                           , choose :: !(Op Int Int e ans)         -- ^ @`perform` choose n` resumes up to @n@ times (returning @1@ up to @n@)
                           }    


-- | Return the first result found in a computation using `choose` for backtracking.
chooseFirst :: Eff (Choose :* e) ans -> Eff e (Maybe ans)
chooseFirst
  = handlerRet Just $
    Choose{ none   = except (\_ -> return Nothing)
          , choose = operation (\hi k -> let try n = if (n > hi) 
                                                      then return Nothing
                                                      else do x <- k n
                                                              case x of
                                                                Nothing -> try (n+1)
                                                                _       -> return x
                                         in try 1)
          }

-- | Return all possible results found in a computation using `choose` for backtracking
chooseAll :: Eff (Choose :* e) a -> Eff e [a]
chooseAll 
  = handlerRet (\x -> [x]) $
    Choose{ none   = except (\_ -> return [])
          , choose = operation (\hi k -> let collect 0 acc = return acc
                                             collect n acc = do xs <- k n
                                                                collect (n-1) $! (xs ++ acc)
                                         in collect hi [])
          }

instance (Choose :? e) => Alternative (Eff e) where
  empty      = perform none ()
  m1 <|> m2  = do x <- perform choose 2
                  if (x==1) then m1 else m2

instance (Choose :? e) => MonadPlus (Eff e) where
  mzero       = perform none ()
  mplus m1 m2 = do x <- perform choose 2
                   if (x==1) then m1 else m2
