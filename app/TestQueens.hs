{-# LANGUAGE TypeOperators, FlexibleContexts, Rank2Types, GADTs
, FlexibleInstances,
 MultiParamTypeClasses
, DataKinds #-}

module TestQueens where


import Criterion.Main

import Control.Monad
import Control.Applicative
import Data.Maybe
import Debug.Trace

import Control.Ev.Eff
import Control.Ev.Util

-- Extensible Effects
import qualified Control.Eff as EE
import qualified Control.Eff.Extend as EEe
import Data.Function (fix)

safeAddition :: [Int] -> Int -> Int -> Bool
safeAddition [] _ _ = True
safeAddition (r:rows) row i =
   row /= r &&
   abs (row - r) /= i &&
   safeAddition rows row (i + 1)

------------------------
-- PURE
------------------------

-- hand-coded solution to the n-queens problem
queensPure :: Int -> [[Int]]
queensPure n = foldM f [] [1..n] where
    f rows _ = [row : rows |
                row <- [1..n],
                safeAddition rows row 1]

------------------------
-- EE
------------------------

data ChooseEE a where
  ChooseEE :: [b] -> ChooseEE b

chooseEE :: (EE.Member (ChooseEE) r) => [b] -> EE.Eff r b
chooseEE xs = EEe.send (ChooseEE xs)

instance EEe.Handle ChooseEE r a (EE.Eff r' (Maybe k)) where
  handle step q (ChooseEE ys) = firstJust ys
     where firstJust xs = case xs of
             []      -> return Nothing
             (x:xs') -> do res <- step (q EEe.^$ x)
                           case res of
                             Nothing -> firstJust xs'
                             _ -> return res

failedEE :: (EE.Member ChooseEE r) => EE.Eff r b
failedEE = chooseEE []

withChooseEE :: Monad m => b -> m (Maybe b)
withChooseEE = return . Just

queensCompEE :: (EE.Member ChooseEE r) => Int -> EE.Eff r [Int]
queensCompEE n = foldM f [] [1..n] where
    f rows _ = do row <- chooseEE [1..n]
                  if (safeAddition rows row 1)
                    then return (row : rows)
                    else failedEE

runChooseEE :: EE.Eff (ChooseEE ': r) a -> EE.Eff r (Maybe a)
runChooseEE = fix (EEe.handle_relay withChooseEE)

queensMaybeEE n = EE.run (runChooseEE (queensCompEE n))

------------------------
-- EFF
------------------------

data Choose e ans = Choose { none   :: (forall a. Op () a e ans)
                           , choose :: (Op Int Int e ans) }


equeens :: (Choose :? e) => Int -> Eff e [Int]
equeens n = foldM f [] [1..n] where
    f rows _ = do row <- perform choose n
                  if (safeAddition rows row 1)
                    then return (row : rows)
                    else perform none ()

chooseFirst :: Eff (Choose :* e) ans -> Eff e (Maybe ans)
chooseFirst
  = handlerRet Just $
    Choose{ none   = except (\_ -> return Nothing)
          , choose = operation (\hi k -> let try n = if (n > hi) 
                                                      then return Nothing
                                                      else do x <- k n
                                                              case x of
                                                                Nothing -> try (n+1)
                                                                _       -> return x
                                         in try 1)
          }

queensMaybe :: Int -> Eff e (Maybe [Int])
queensMaybe n = chooseFirst $ equeens n


------------------------
-- FIRST
------------------------

newtype Q e a = Q [Eff (Local (Q e a) :* e) (Maybe a)]

chooseFirstQ :: Eff (Choose :* e) a -> Eff e (Maybe a)
chooseFirstQ =  handlerLocalRet (Q []) (\x _ -> Just x) $
               Choose{ none   = except (\_ -> step)
                     , choose = operation (\hi k -> do (Q q) <- localGet
                                                       localPut (Q (map k [1..hi] ++ q))
                                                       step)
                     }

step :: Eff (Local (Q e a) :* e) (Maybe a)
step     = do (Q q) <- localGet
              case q of
                (m:ms) -> do localPut (Q ms)
                             m                             
                []     -> return Nothing

queensMaybeQ :: Int -> Eff () (Maybe [Int])
queensMaybeQ n = chooseFirstQ $ equeens n


------------------------
--

pureTest       n = head $ queensPure n
maybeTest      n = runEff $ queensMaybe n
maybeQTest      n = runEff $ queensMaybeQ n
maybeTestEE    n = queensMaybeEE n

comp n = [ bench "pure"          $ whnf pureTest n
         , bench "effect maybe"   $ whnf maybeTest n
         , bench "effect maybe queue "  $ whnf maybeQTest n
         , bench "ee maybe"       $ whnf maybeTestEE n
         ]


main :: IO ()
main = defaultMain
       [ bgroup "20" (comp 20) ]
