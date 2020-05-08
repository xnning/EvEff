{-# LANGUAGE
    FlexibleContexts
  , AllowAmbiguousTypes -- Extensible Effects
#-}
module TestState where

import Criterion.Main
import Criterion.Types
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
-- IOREF
-------------------------------------------------------

refCount :: Int -> Int
refCount init
  = let l = unsafePerformIO (newIORef init)
    in runRefCount l

runRefCount :: IORef Int -> Int
runRefCount r
  = let x = localGet r
    in if (x == 0) then x else seq (localSet r (x - 1)) (runRefCount r)

{-# INLINE unsafeIO #-}
unsafeIO :: IO a -> a
unsafeIO io = let x = unsafePerformIO io in seq x x

{-# INLINE localGet #-}
localGet :: IORef a -> a
localGet r = unsafeIO (readIORef r)

{-# INLINE localSet #-}
localSet :: IORef a -> a -> ()
localSet r x = unsafeIO (writeIORef r x)


ioRefCount :: Int -> IO Int
ioRefCount init
  = do r <- newIORef init
       ioLoop r

ioLoop r
  = do i <- readIORef r
       if (i==0) then return i else do writeIORef r (i - 1); ioLoop r

-------------------------------------------------------
-- TESTS
-------------------------------------------------------

ppure          n = bench "pure"    $ whnf runPure    n
monadic        n = bench "monadic" $ whnf runMonadic n

effPlain n = bench "eff plain state"   $ whnf count n
effPar   n = bench "eff parameterized" $ whnf pCount n
effLo    n = bench "eff local"         $ whnf lCount n

ext    n = bench "extensible effects "       $ whnf runExtEff n

testRefCount   n = bench "refCount"          $ whnf refCount n
testIORefCount n = bench "ioRefCount"        $ whnfIO (ioRefCount n)


comp n  = [ ppure n
          , monadic n
          , effPlain n
          , effLo n
          , effPar n
          , ext n ]
iterExp = 6


main :: IO ()
main = defaultMain
       [ bgroup ("2*10^" ++ (show m)) (comp (2*10^m)) | let m = iterExp ]
