{-# LANGUAGE RankNTypes, FlexibleContexts, TypeOperators, UndecidableInstances #-}
{-|
Description : Definitions for monad effects.
Copyright   : (c) 2021 Jaro Reinders
License     : MIT
Maintainer  : xnning@hku.hk; daan@microsoft.com
Stability   : Experimental

Some definitions for monad effects.

The effect monad can include at most one other monad effect.
A common effect to include is the IO effect, which allows you to run IO actions
in your effect monad.

But note that it this module is intended to be used for implementing other
more granular effects. For example, instead of running @putStrLn@ directly in
the effect monad, consider defining a @Console@ effect:

@
data Console e ans = Console { print :: Op String () e ans }
@

Then you can use the functionality in this module to implement the effect
handler:

@
console :: IOEff :? e => Eff (Console :* e) a -> Eff e a
console = handler Console { print = function (performIO . putStrLn) }
@
-}
module Control.Ev.Monad
  (
  -- * Monad effect
    MEff(MEff)
  , performM
  , runMEff
  -- * IO effect
  , IOEff
  , performIO
  , runIOEff
  ) where

import           Control.Ev.Eff
import           Control.Monad.IO.Class

------------------
-- Monad effect --
------------------

-- | An effect for embedding another monad @m@ into the effect monad.
newtype MEff m e ans = MEff
    { meff :: forall a. Op (m a) a e ans
    }

-- | Perform a different monadic action in the effect monad.
performM :: MEff m :? e => m a -> Eff e a
performM = perform meff

-- | Run an effect monad with a single other monadic effect.
--
-- All other effects need to be handled before this function can be used to
-- get the final result.
runMEff :: Monad m => Eff (MEff m :* ()) a -> m a
runMEff = runEff . handlerRet
  pure
  MEff { meff = operation $ \a k -> pure $ a >>= runEff . k }

---------------
-- IO effect --
---------------

-- | An effect for embedding @IO@ into the effect monad.
type IOEff = MEff IO

-- | Perform an @IO@ action in the effect monad.
performIO :: IOEff :? e => IO a -> Eff e a
performIO = performM

-- | Run an effect monad that has a single @IO@ effect.
--
-- All other effects need to be handled before this function can be used to
-- get the final result.
runIOEff :: Eff (IOEff :* ()) a -> IO a
runIOEff = runMEff

instance IOEff :? e => MonadIO (Eff e) where
  liftIO = performIO
