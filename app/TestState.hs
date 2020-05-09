{-# LANGUAGE
    FlexibleContexts
  , TypeOperators
  , AllowAmbiguousTypes -- Extensible Effects
#-}
module TestState where

import Criterion.Main
import Criterion.Types
import qualified EffEvScoped as E
import Library hiding (main)

import qualified Control.Monad.State as Ms

-- Extensible Effects
import qualified Control.Eff as EE
import qualified Control.Eff.State.Lazy as EEs

import EffEvScopedLocalHide

-------------------------------------------------------
-- PURE
-------------------------------------------------------

runPure :: Int -> Int
runPure n = if n == 0 then n
            else runPure (n-1)

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
-- EFF LCOAL NON TAIL
-------------------------------------------------------

lCountNonTail :: Int -> Int
lCountNonTail n = E.erun $ lstateNonTail n $
           do x <- runCount ()
              return x

-------------------------------------------------------
-- EFF Safe local
-------------------------------------------------------

data StateL a e ans = StateL { getl :: Op () a e ans, setl :: Op a () e ans }

statel :: a -> Eff (StateL a :* e) ans -> Eff e ans
statel init
  = handlerLocal init (StateL{ getl = function (\() -> localGet), setl = function (\x -> localSet x) })

countl :: (StateL Int :? e) => () -> Eff e Int
countl ()
  = do i <- perform getl ()
       if (i==0) then return i
        else do perform setl (i - 1)
                countl ()

runCountl :: Int -> Int
runCountl n = erun $ statel n $ countl ()


countl2 :: (StateL Int :? e) => Eff e Int
countl2
  = do i <- perform getl ()
       if (i==0) then return i
        else do perform setl (i - 1)
                countl2

runCountl2 :: Int -> Int
runCountl2 n = erun $ statel n $ countl2

-------------------------------------------------------
-- TESTS
-------------------------------------------------------

ppure          n = bench "pure"    $ whnf runPure    n
monadic        n = bench "monadic" $ whnf runMonadic n

effPlain n = bench "eff plain state"    $ whnf count n
effPar   n = bench "eff parameterized"  $ whnf pCount n
effLo    n = bench "eff local"          $ whnf lCount n
effLoNt  n = bench "eff local non tail" $ whnf lCountNonTail n
effLoc   n = bench "eff safe local "     $ whnf runCountl n
effLoc2  n = bench "eff safe local; no unit "     $ whnf runCountl2 n

ee       n = bench "extensible effects "     $ whnf runEE n


comp n  = [ ppure n
          , monadic n
          , effLoc n
          , effLoc2 n
          , effPlain n
          , effPar n
          , effLo n
          , effLoNt n
          , ee n ]
iterExp = 7


main :: IO ()
main = defaultMain
       [ bgroup ("10^" ++ (show m)) (comp (10^m)) | let m = iterExp ]
