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
import qualified Control.Eff.State.Strict as EEs
import qualified Control.Eff.Logic.NDet as EEn

import Control.Ev.Eff
import Control.Ev.Util

pyth20 =
  [(3,4,5),(4,3,5),(5,12,13),(6,8,10),(8,6,10),(8,15,17),(9,12,15),(12,5,13),
   (12,9,15),(12,16,20),(15,8,17),(16,12,20)]

-------------------------------------------------------
-- PURE
-------------------------------------------------------

res :: ([(Int, Int, Int)], Int) -> Int
res x = length (fst x)

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

pythState :: Int -> ContT [r] (Ms.State Int) (Int, Int, Int)
pythState upbound = do
  x <- stream 1 upbound
  y <- stream 1 upbound
  z <- stream 1 upbound
  cnt <- Ms.get
  Ms.put $ (cnt + 1)
  if x*x + y*y == z*z then return (x,y,z) else mzero

pythMonadicState :: Int -> Int
pythMonadicState n = res $ Ms.runState (runContT (pythState n) (\x -> return [x])) 0

-------------------------------------------------------
-- EXTENSIBLE EFFECTS
-------------------------------------------------------

testEE = pyth20 == ((EE.run . EEn.makeChoiceA $ pyth 20) :: [(Int,Int,Int)])

pythEESlow n = length $
            ((EE.run . EEn.makeChoiceA0 $ pyth n) :: [(Int,Int,Int)])

pythEEFast n = length $
            ((EE.run . EEn.makeChoiceA $ pyth n) :: [(Int,Int,Int)])

pythStateE :: (EE.Member (EEs.State Int) r, EE.Member EEn.NDet r) =>
          Int -> EE.Eff r (Int, Int, Int)
pythStateE upbound = do
  x <- stream 1 upbound
  y <- stream 1 upbound
  z <- stream 1 upbound
  cnt <- EEs.get
  EEs.put $ (cnt + 1 ::Int)
  if x*x + y*y == z*z then return (x,y,z) else mzero

pythEEStateSlow :: Int -> Int
pythEEStateSlow n = res $ EE.run $ EEs.runState 0 (EEn.makeChoiceA0 $ pythStateE n)

pythEEStateFast :: Int -> Int
pythEEStateFast n = res $ EE.run $ EEs.runState 0 (EEn.makeChoiceA $ pythStateE n)

-------------------------------------------------------
-- EFF
-------------------------------------------------------

epyth :: (Choose :? e) => Int -> Eff e (Int, Int, Int)
epyth upbound = do
  x <- perform choose upbound
  y <- perform choose upbound
  z <- perform choose upbound
  if (x*x + y*y == z*z) then return (x,y,z) else perform none ()

runPythEff :: Int -> ([(Int,Int,Int)])
runPythEff n = runEff $ chooseAll $ epyth n

testEff = pyth20 == (runPythEff 20)

pythEff n = length $ (runPythEff n)

epythState :: (Choose :? e, State Int :? e) => Int -> Eff e (Int, Int, Int)
epythState upbound = do
  x <- perform choose upbound
  y <- perform choose upbound
  z <- perform choose upbound
  cnt <- perform get ()
  perform put (cnt + 1 :: Int)
  if (x*x + y*y == z*z) then return (x,y,z) else perform none ()

pythEffState :: Int -> Int
pythEffState n = length $ runEff $ state (0::Int) $ chooseAll $ epythState n

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

chooseAllQ :: Eff (Choose :* e) a -> Eff e [a]
chooseAllQ =   handlerLocalRet (Q []) (\x _ -> [x]) $
               Choose{ none = except (\x -> do (Q q) <- localGet
                                               case q of
                                                 (m:ms) -> do localPut (Q ms)
                                                              m
                                                 []     -> return [])
                     , choose = operation (\hi k -> do (Q q) <- localGet
                                                       localPut (Q (map k [1..hi] ++ q))
                                                       steps)
                     }

steps :: Eff (Local (Q e a) :* e) [a]
steps  = do (Q q) <- localGet
            case q of
              (m:ms) -> do localPut (Q ms)
                           xs <- m
                           ys <- steps
                           return (xs ++ ys)
              []     -> return []

testEffQ = pyth20 == ((runEff $ chooseAllQ $ epyth 20) :: [(Int,Int,Int)])

pythEffQ n = length $
                ((runEff $ chooseAllQ $ epyth n) :: [(Int,Int,Int)])


-------------------------------------------------------
-- TEST
-------------------------------------------------------

comp n = [ bench "pure"                    $ whnf pythPure n
         , bench "monadic"                 $ whnf pythMonadic n
         -- , bench "extensible effects slow" $ whnf pythEESlow n
         , bench "extensible effects fast" $ whnf pythEEFast n
         , bench "eff"  $ whnf pythEff n
         -- , bench "eff queue"  $ whnf pythEffQ n

         -- with state
         , bench "state monadic"                 $ whnf pythMonadicState n
         -- , bench "extensible effects slow" $ whnf pythEESlow n
         , bench "state extensible effects fast" $ whnf pythEEStateFast n
         , bench "state eff"                     $ whnf pythEffState n
         ]

num :: Int
num = 250

main :: IO ()
main = defaultMain
       [ bgroup (show num) (comp num) ]
