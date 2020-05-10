{-# LANGUAGE
    FlexibleContexts
  , TypeOperators
  , AllowAmbiguousTypes -- Extensible Effects
#-}
module TestState where

import Criterion.Main
import Criterion.Types
-- import Library hiding (main)

import qualified Control.Monad.State as Ms

-- Extensible Effects
import qualified Control.Eff as EE
import qualified Control.Eff.State.Lazy as EEs

import Control.Ev.Eff
import Control.Ev.Util

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

countEE :: (EE.Member (EEs.State Int) r) => () -> EE.Eff r Int
countEE ()= do n <- EEs.get
               if n == 0 then return n
               else do EEs.put (n - 1)
                       countEE ()

runEE n = EEs.runState n (countEE ())

-------------------------------------------------------
-- Eff local tail
-------------------------------------------------------

-- runCount :: () -> Eff (State Int :* e) Int
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
  = handlerLocal init (State{ get = operation (\() k -> do{ x <- localGet; k x }),
                              put = operation (\x k  -> do{ localSet x; k () }) })

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


-- runCount :: () -> Eff (State Int :* e) Int
runCountLoc :: Eff (Local Int :* e) Int
runCountLoc
  = do i <- localGet
       if (i==0) then return i
        else do localSet (i - 1)
                runCountLoc


countLoc :: Int -> Int
countLoc n
  = runEff $ local n $ runCountLoc



-------------------------------------------------------
-- TESTS
-------------------------------------------------------

ppure     n = bench "pure"    $ whnf runPure    n
monadic   n = bench "monadic" $ whnf runMonadic n
ee        n = bench "extensible effects "     $ whnf runEE n

effFun    n = bench "eff functional state" $ whnf countFun n
effLoc    n = bench "eff local"            $ whnf countTail n
effLocNt  n = bench "eff local non tail"   $ whnf countNonTail n
effLocal  n = bench "eff local builtin"    $ whnf countLoc n

comp n  = [ ppure n
          , monadic n
          , ee n
          , effLocal n
          , effLoc n
          , effLocNt n
          , effFun n
          ]

iterExp = 7

main :: IO ()
main = defaultMain
       [ bgroup ("10^" ++ (show m)) (comp (10^m)) | let m = iterExp ]
