module TestState where

import Criterion.Main
import Criterion.Types
import Library hiding (main)

import Data.IORef
import System.IO.Unsafe ( unsafePerformIO )

import qualified Control.Monad.State as M


countPure :: Int -> Int
countPure n = if n == 0 then n
              else countPure (n-1)

countMonadic :: M.State Int Int
countMonadic =
  do {n <- M.get;
      if n == 0 then return n
      else do {M.put (n-1); countMonadic}}

runMonadic = M.runState countMonadic
runPure    = countPure


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

ppure   n = bench "pure"    $ whnf runPure    n
monadic n = bench "monadic" $ whnf runMonadic n

effevscoped    n = bench "effevscoped"               $ whnf count n
effevscopedPar n = bench "effevscoped parameterized" $ whnf pCount n
effevscopedLo  n = bench "effevscoped local"         $ whnf lCount n
testRefCount   n = bench "refCount"                  $ whnf refCount n
testIORefCount   n = bench "ioRefCount"              $ whnfIO (ioRefCount n)


comp n = -- [monadic n, effevscopedLo n, testRefCount n, testIORefCount n] -- , effevscopedPar n] -- ppure n, monadic n, effevscopedLo n]
         [effevscopedLo n]
iterExp = 6


main :: IO ()
main = defaultMain
       [ bgroup ("2*10^" ++ (show m)) (comp (2*10^m)) | let m = iterExp ]
