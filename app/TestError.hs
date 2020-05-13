{-# LANGUAGE FlexibleContexts #-}

module TestError where

import Criterion.Main
import Criterion.Types

-- MTL
import Control.Monad
import qualified Control.Monad.Except as Me

-- Extensible Effects
import qualified Control.Eff as EE
import qualified Control.Eff.Exception as EEe

-- Fused Effects
import qualified Control.Algebra as F
import qualified Control.Carrier.Error.Either as Fe

-- Eff
import Control.Ev.Eff
import qualified Control.Ev.Util as E

list :: Int -> [Int]
list n = replicate n 1 ++ [0]

errorPure n = product $ list n

errorMonadic :: Int -> Int
errorMonadic n = either id id m
 where
 m = foldM f 1 (list n)
 f acc 0 = Me.throwError 0
 f acc x = return $ acc * x

errorEE :: Int -> Int
errorEE n = either id id . EE.run . EEe.runError $ m
 where
 m = foldM f 1 (list n)
 f acc 0 = EEe.throwError (0::Int)
 f acc x = return $ acc * x

errorF :: Int -> Int
errorF n = either id id . F.run . Fe.runError $ m
 where
 m = foldM f 1 (list n)
 f acc 0 = Fe.throwError (0::Int)
 f acc x = return $ acc * x

errorEff :: Int -> Int
errorEff n = either id id . runEff . E.exceptEither $ m
 where
 m = foldM f 1 (list n)
 f acc 0 = perform E.throwError (0::Int)
 f acc x = return $ acc * x

ppure     n = bench "pure"                    $ whnf errorPure    n
monadic   n = bench "monadic"                 $ whnf errorMonadic n
ee        n = bench "extensible effects "     $ whnf errorEE n
fe        n = bench "fused effects"           $ whnf errorF n
eff       n = bench "eff"                     $ whnf errorEff n

comp n  = [ ppure n
          , monadic n
          , ee n
          , fe n
          , eff n
          ]

num = 10000000

main :: IO ()
main = defaultMain
       [ bgroup (show num) (comp num) ]
