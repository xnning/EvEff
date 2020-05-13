{-# LANGUAGE
    FlexibleContexts
  , TypeOperators
  , AllowAmbiguousTypes -- Extensible Effects
#-}
module TestState where

import Control.Monad.ST
import Data.STRef

import Criterion.Main
import Criterion.Types
-- import Library hiding (main)

import qualified Control.Monad.State as Ms

-- Extensible Effects
import qualified Control.Eff as EE
import qualified Control.Eff.State.Strict as EEs

-- Fused Effects
import qualified Control.Algebra as F
import qualified Control.Carrier.State.Strict as Fs

import Control.Ev.Eff
import Control.Ev.Util

-------------------------------------------------------
-- PURE
-------------------------------------------------------

runPure :: Int -> Int
runPure n = if n == 0 then n
            else runPure (n-1)


countST :: STRef s Int -> ST s Int
countST r
  = do i <- readSTRef r
       if (i==0) then return i
        else do writeSTRef r (i-1)
                countST r


runCountST :: Int -> Int
runCountST n
  = runST $ do r <- newSTRef n
               countST r

-------------------------------------------------------
-- MONADIC
-------------------------------------------------------

countMonadic :: Ms.State Int Int
countMonadic =
  do n <- Ms.get
     if n == 0 then return n
     else do Ms.put (n-1)
             countMonadic

runMonadic = Ms.runState countMonadic

-------------------------------------------------------
-- EXTENSIBLE EFFECTS
-------------------------------------------------------

countEE :: (EE.Member (EEs.State Int) r) => EE.Eff r Int
countEE = do n <- EEs.get
             if n == 0 then return n
              else do EEs.put (n - 1)
                      countEE

runEE n = EEs.runState n countEE

-------------------------------------------------------
-- FUSED EFFECTS
-------------------------------------------------------

countF :: (F.Has (Fs.State Int) sig m ) => m Int
countF = do n <- Fs.get
            if n == 0 then return n
            else do Fs.put (n - 1)
                    countF

runCountF n = F.run $ Fs.runState n countF

-------------------------------------------------------
-- Eff local tail
-------------------------------------------------------

-- runCount :: Eff (State Int :* e) Int
runCount :: (State Int :? e) =>  Eff e Int
runCount
  = do i <- perform get ()
       if (i==0) then return i
        else do perform put (i - 1)
                runCount


countTail :: Int -> Int
countTail n
  = runEff $ state n $ runCount


stateNonTail :: a -> Eff (State a :* e) ans -> Eff e ans
stateNonTail init
  = handlerLocal init (State{ get = operation (\() k -> do{ x <- perform lget (); k x }),
                              put = operation (\x k  -> do{ perform lput x; k () }) })

countNonTail :: Int -> Int
countNonTail n
  = runEff $ stateNonTail n $ runCount


stateFun :: a -> Eff (State a :* e) ans -> Eff e ans
stateFun init action
  = do f <- handler (State { get = operation (\() k -> return $ \s -> (k s  >>= \r -> r s ))
                           , put = operation (\s  k -> return $ \_ -> (k () >>= \r -> r s))
                           })
                    (do x <- action
                        return (\s -> return x))
       f init

countFun :: Int -> Int
countFun n
  = runEff $ stateFun n $ runCount


runCountBuiltin :: (Local Int :? e) => Eff e Int
runCountBuiltin
  = do i <- perform lget () --localGet
       if (i==0) then return i
        else do -- localPut (i - 1)
                perform lput (i - 1)
                runCountBuiltin


countBuiltin :: Int -> Int
countBuiltin n
  = runEff $ local n $ runCountBuiltin

{-
runCountLinear :: (Linear (State Int) :? e) =>  Eff e Int
runCountLinear
  = do i <- lperform get ()
       if (i==0) then return i
        else do lperform put (i - 1)
                runCountLinear


countLinear :: Int -> Int
countLinear n
  = runEff $ lstate n $ runCountLinear
-}
-------------------------------------------------------
-- TESTS
-------------------------------------------------------

ppure     n = bench "pure"    $ whnf runPure    n
monadic   n = bench "monadic" $ whnf runMonadic n
ee        n = bench "extensible effects "     $ whnf runEE n
st        n = bench "runST"   $ whnf runCountST n

effFun    n = bench "eff functional state" $ whnf countFun n
effLoc    n = bench "eff local"            $ whnf countTail n
effLocNt  n = bench "eff local non tail"   $ whnf countNonTail n
effBuiltin n = bench "eff local builtin"    $ whnf countBuiltin n
-- effLinear  n = bench "eff local linear"     $ whnf countLinear n
fe        n  = bench "fused effects"        $ whnf runCountF n

comp n  = [ ppure n
          , monadic n
          , st n
          , ee n
          , effBuiltin n
--          , effLinear n
          , effLoc n
          , effLocNt n
          , effFun n
          , fe n
          ]

iterExp = 7

main :: IO ()
main = defaultMain
       [ bgroup ("10^" ++ (show m)) (comp (10^m)) | let m = iterExp ]
