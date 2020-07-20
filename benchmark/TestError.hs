{-# LANGUAGE FlexibleContexts,TypeOperators #-}
{-|
Description : Benchmark exception
Copyright   : (c) 2020, Microsoft Research; Daan Leijen; Ningning Xie
License     : MIT
Maintainer  : xnning@hku.hk; daan@microsoft.com
Stability   : Experimental

Original benchmark from 
-}
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
errorMonadic n = either id id $ errMonadic n

errMonadic :: Me.MonadError Int m => Int -> m Int
errMonadic n = foldM f 1 (list n)
             where 
               f acc 0 = Me.throwError (0::Int)
               f acc x = return (acc * x)

errorEE :: Int -> Int
errorEE n = either id id $ EE.run $ EEe.runError $ errEE n

errEE :: (EE.Member (EEe.Exc Int) e) => Int -> EE.Eff e Int
errEE n = foldM f 1 (list n)
        where 
         f acc 0 = EEe.throwError (0::Int)
         f acc x = return (acc * x) 
 

errorF :: Int -> Int
errorF n = either id id $ F.run $ Fe.runError $ errF n

errF :: (F.Has (Fe.Error Int) sig m ) => Int -> m Int
errF n = foldM f 1 (list n)
       where 
         f acc 0 = Fe.throwError (0::Int)
         f acc x = return (acc * x)

errorEff :: Int -> Int
errorEff n = either id id $ runEff $ E.exceptEither $ errEff n
  
errEff :: (E.Except Int :? e) => Int -> Eff e Int
errEff n = foldM f 1 (list n)
         where
          f acc 0 = perform E.throwError (0::Int)
          f acc x = return (acc * x)


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
