{-# LANGUAGE FlexibleContexts #-}

module TestError where

import Criterion.Main
import Criterion.Types

import Control.Monad
import qualified Control.Eff as EE
import qualified Control.Monad.Except as Me
import qualified Control.Eff.Exception as EEe

import Control.Ev.Eff
import qualified Control.Ev.Util as E

be_make_list :: Int -> [Int]
be_make_list n = replicate n 1 ++ [0]

errorPure n = product $ be_make_list n

errorMonadic :: Int -> Int
errorMonadic n = either id id m
 where
 m = foldM f 1 (be_make_list n)
 f acc 0 = Me.throwError 0
 f acc x = return $! acc * x

errorEE :: Int -> Int
errorEE n = either id id . EE.run . EEe.runError $ m
 where
 m = foldM f 1 (be_make_list n)
 f acc 0 = EEe.throwError (0::Int)
 f acc x = return $! acc * x

errorEff :: Int -> Int
errorEff n = either id id . runEff . E.exceptEither $ m
 where
 m = foldM f 1 (be_make_list n)
 f acc 0 = perform E.throwError (0::Int)
 f acc x = return $! acc * x

ppure     n = bench "pure"                    $ whnf errorPure    n
monadic   n = bench "monadic"                 $ whnf errorMonadic n
ee        n = bench "extensible effects "     $ whnf errorEE n
eff       n = bench "eff"                     $ whnf errorEff n

comp n  = [ ppure n
          , monadic n
          , ee n
          , eff n
          ]

num = 10000000

main :: IO ()
main = defaultMain
       [ bgroup (show num) (comp num) ]
