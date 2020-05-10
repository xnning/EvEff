{-# LANGUAGE
    FlexibleContexts
  , AllowAmbiguousTypes -- Extensible Effects
  , TypeOperators
  , FlexibleInstances
  , UndecidableInstances
  , RankNTypes
#-}
module TestPyth where

import Criterion.Main
import Criterion.Types
-- import Library hiding (main)

import Control.Monad (foldM)
import qualified Control.Monad.State as Ms
import qualified Control.Monad.Reader as Mr
import Control.Monad.Cont as Mc
import GHC.Base

-- Extensible Effects
import qualified Control.Eff as EE
import qualified Control.Eff.State.Lazy as EEs
import qualified Control.Eff.Reader.Lazy as EEr
import qualified Control.Eff.Logic.NDet as EEn

import Control.Ev.Eff

pyth20 =
  [(3,4,5),(4,3,5),(5,12,13),(6,8,10),(8,6,10),(8,15,17),(9,12,15),(12,5,13),
   (12,9,15),(12,16,20),(15,8,17),(16,12,20)]

-------------------------------------------------------
-- MONADIC
-------------------------------------------------------

-- Stream from k to n
stream k n = if k > n then mzero else return k `mplus` stream (k+1) n

pyth :: MonadPlus m => Int -> m (Int, Int, Int)
pyth upbound = do
  x <- stream 1 upbound
  y <- stream 1 upbound
  z <- stream 1 upbound
  if x*x + y*y == z*z then return (x,y,z) else mzero

instance Monad m => Alternative (ContT [r] m) where
  empty = mzero
  (<|>) = mplus

instance Monad m => MonadPlus (ContT [r] m) where
  mzero = ContT $ \k -> return []
  mplus (ContT m1) (ContT m2) = ContT $ \k ->
    liftM2 (++) (m1 k) (m2 k)


testMonadic = pyth20 == ((runCont (pyth 20) (\x -> [x])) :: [(Int,Int,Int)])

pythMonadic n = length $ ((runCont (pyth n) (\x -> [x])) :: [(Int,Int,Int)])

-------------------------------------------------------
-- EXTENSIBLE EFFECTS
-------------------------------------------------------

testEE = pyth20 == ((EE.run . EEn.makeChoiceA $ pyth 20) :: [(Int,Int,Int)])

pythEESlow n = length $
            ((EE.run . EEn.makeChoiceA0 $ pyth n) :: [(Int,Int,Int)])

pythEEFast n = length $
            ((EE.run . EEn.makeChoiceA $ pyth n) :: [(Int,Int,Int)])

-------------------------------------------------------
-- EFF
-------------------------------------------------------

data NDet e ans = NDet { zero :: forall a. Op () a e ans
                       , plus :: Op () Bool e ans }


instance (NDet :? e) => Alternative (Eff e) where
  empty = mzero
  (<|>) = mplus

instance (NDet :? e) => MonadPlus (Eff e) where
  mzero = perform zero ()
  mplus m1 m2 = do x <- perform plus ()
                   if x then m1 else m2

-- slow version
makeChoiceA0 :: Alternative f => Eff (NDet :* e) a -> Eff e (f a)
makeChoiceA0 =  handlerRet pure
                   NDet{ zero = operation (\_ _ -> return empty)
                       , plus = operation (\_ k -> liftM2 (<|>) (k True) (k False))
                       }

-- do we have a fast version? hmm

testEff = pyth20 == ((runEff $ makeChoiceA0 $ pyth 20) :: [(Int,Int,Int)])

pythEff n = length $
            ((runEff $ makeChoiceA0 $ pyth n) :: [(Int,Int,Int)])

-------------------------------------------------------
-- TEST
-------------------------------------------------------

comp n = [ bench "monadic"            $ whnf pythMonadic n
         , bench "extensible effects slow" $ whnf pythEESlow n
         , bench "extensible effects fast" $ whnf pythEEFast n
         , bench "eff"                $ whnf pythEff n
         ]

num :: Int
num = 250

main :: IO ()
main = defaultMain
       [ bgroup (show num) (comp num) ]
