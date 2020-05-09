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

import Data.IORef
import System.IO.Unsafe ( unsafePerformIO )

import qualified Control.Monad.State as M

-- "extensible effects"
import qualified Control.Eff as F
import qualified Control.Eff.State.Lazy as FS

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
effLoc   n = bench "eff safe local "     $ whnf runCountl n


comp n  = [ ppure n
          , monadic n
          , ext n
          , effLoc n
          , effPlain n
          , effPar n
          , effLo n
          , effLoNt n
          ]
iterExp = 6


main :: IO ()
main = defaultMain
       [ bgroup ("2*10^" ++ (show m)) (comp (2*10^m)) | let m = iterExp ]
