{-# LANGUAGE
    FlexibleContexts
  , AllowAmbiguousTypes -- Extensible Effects
#-}
module TestState where

import Criterion.Main
import Criterion.Types
import EffEvScoped
import Library hiding (main)

import Data.IORef
import System.IO.Unsafe ( unsafePerformIO )

import qualified Control.Monad.State as M

-- "extensible effects"
import qualified Control.Eff as F
import qualified Control.Eff.State.Lazy as FS


-------------------------------------------------------
-- PURE
-------------------------------------------------------

runPure :: Int -> Int
runPure n = if n == 0 then n
            else runPure (n-1)

-------------------------------------------------------
-- MONADIC
-------------------------------------------------------

countMonadic :: M.State Int Int
countMonadic =
  do n <- M.get
     if n == 0 then return n
     else do M.put (n-1)
             countMonadic

runMonadic = M.runState countMonadic

-------------------------------------------------------
-- EXTENSIBLE EFFECTS
-------------------------------------------------------

countExtEff :: (F.Member (FS.State Int) r) => F.Eff r Int
countExtEff = do n <- FS.get
                 if n == 0 then return n
                 else do FS.put (n - 1);
                         countExtEff

runExtEff n = FS.runState n countExtEff

-------------------------------------------------------
-- EFF LCOAL NON TAIL
-------------------------------------------------------

lCountNonTail :: Int -> Int
lCountNonTail n = erun $ lstateNonTail n $
           do x <- runCount ()
              return x

-------------------------------------------------------
-- TESTS
-------------------------------------------------------

ppure          n = bench "pure"    $ whnf runPure    n
monadic        n = bench "monadic" $ whnf runMonadic n

effPlain n = bench "eff plain state"    $ whnf count n
effPar   n = bench "eff parameterized"  $ whnf pCount n
effLo    n = bench "eff local"          $ whnf lCount n
effLoNt  n = bench "eff local non tail" $ whnf lCountNonTail n

ext      n = bench "extensible effects "     $ whnf runExtEff n


comp n  = [ ppure n
          , monadic n
          , effPlain n
          , effPar n
          , effLo n
          , effLoNt n
          , ext n ]
iterExp = 6


main :: IO ()
main = defaultMain
       [ bgroup ("2*10^" ++ (show m)) (comp (2*10^m)) | let m = iterExp ]
