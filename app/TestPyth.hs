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
import qualified Control.Monad.State as Ms hiding (mapM)
import qualified Control.Monad.Reader as Mr hiding (mapM)
import Control.Monad.Cont as Mc hiding (mapM)
import GHC.Base hiding (mapM)

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
-- PURE
-------------------------------------------------------

pythPure upbound = length $
  [ (x, y, z) | x <- [1..upbound]
              , y <- [1..upbound]
              , z <- [1..upbound]
              , x*x + y*y == z*z
              ]

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
-------------------------------------------------------
-- EFF
-------------------------------------------------------

data NDet e ans = NDet { zero :: !(forall a. Op () a e ans)
                       , pick :: !(Op Int Int e ans) }


epyth :: (NDet :? e) => Int -> Eff e (Int, Int, Int)
epyth upbound = do
 x <- perform pick upbound
 y <- perform pick upbound
 z <- perform pick upbound
 if (x*x + y*y == z*z) then return (x,y,z) else perform zero ()

-- slow version
makeChoiceA0 :: Eff (NDet :* e) a -> Eff e [a]
makeChoiceA0 =  handlerRet (\x -> [x])
                   NDet{ zero = except (\_ -> return [])
                       , pick = operation (\hi k -> let collect acc 0 = return (concat acc)
                                                        collect acc n = do x <- k n
                                                                           collect (x:acc) (n-1)
                                                    in collect [] hi)
                       }



runPythEff :: Int -> ([(Int,Int,Int)])
runPythEff n = runEff $ makeChoiceA0 $ epyth n

testEff = pyth20 == (runPythEff 20)

pythEff n = length $ (runPythEff n)

{-
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
makeChoiceA0 :: Alternative m => Eff (NDet :* e) a -> Eff e (m a)
makeChoiceA0 =  handlerRet pure
                   NDet{ zero = operation (\_ _ -> return empty)
                       , plus = operation (\_ k -> liftM2 (<|>) (k True) (k False))
                       }


testEff = pyth20 == ((runEff $ makeChoiceA0 $ pyth 20) :: [(Int,Int,Int)])

pythEff n = length $
           ((runEff $ makeChoiceA0 $ pyth n) :: [(Int,Int,Int)])
-}



-- do we have a fast version? hmm

newtype Q e a = Q [Eff (Local (Q e a) :* e) [a]]

makeChoiceA :: Eff (NDet :* e) a -> Eff e [a]
makeChoiceA =  handlerLocalRet (Q []) (\x _ -> [x]) $
               NDet{ zero = operation (\_ _ -> step)
                   , pick = operation (\hi k -> do (Q q) <- localGet
                                                   localPut (Q (map k [1..hi] ++ q))
                                                   step)
                   }

step :: Eff (Local (Q e a) :* e) [a]
step     = do (Q q) <- localGet
              case q of
                (m:ms) -> do localPut (Q ms)
                             xs <- m
                             ys <- step
                             return (xs ++ ys)
                []     -> return []

testEffFast = pyth20 == ((runEff $ makeChoiceA $ epyth 20) :: [(Int,Int,Int)])

pythEffFast n = length $
                ((runEff $ makeChoiceA $ epyth n) :: [(Int,Int,Int)])


-------------------------------------------------------
-- TEST
-------------------------------------------------------

comp n = [ bench "pure"                    $ whnf pythPure n
         --, bench "monadic"                 $ whnf pythMonadic n
         --, bench "extensible effects slow" $ whnf pythEESlow n
         , bench "extensible effects fast" $ whnf pythEEFast n
         , bench "eff slow"  $ whnf pythEff n
         --, bench "eff fast"  $ whnf pythEffFast n
         ]

num :: Int
num = 250

main :: IO ()
main = defaultMain
       [ bgroup (show num) (comp num) ]
