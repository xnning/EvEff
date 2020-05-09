{-# LANGUAGE TypeOperators, FlexibleContexts, Rank2Types #-}

module TestQueens where


import Criterion.Main

import Control.Monad
import Control.Applicative
import Data.Maybe
import EffEvScoped
import Debug.Trace
import Library hiding (main)

safeAddition :: [Int] -> Int -> Int -> Bool
safeAddition [] _ _ = True
safeAddition (r:rows) row i =
   row /= r &&
   abs (row - r) /= i &&
   safeAddition rows row (i + 1)

-- hand-coded solution to the n-queens problem
queensPure :: Int -> [[Int]]
queensPure n = foldM f [] [1..n] where
    f rows _ = [row : rows |
                row <- [1..n],
                safeAddition rows row 1]

------------------------
-- Choose
------------------------

data Choose e ans = Choose { choose_ :: forall b. Op [b] b e ans }

choose :: (Choose :? e) => [b] -> Eff e b
choose xs = perform choose_ xs


failed :: (Choose :? e) => Eff e b
failed = choose []

queensComp :: (Choose :? e) => Int -> Eff e [Int]
queensComp n = foldM f [] [1..n] where
    f rows _ = do row <- choose [1..n]
                  if (safeAddition rows row 1)
                    then return (row : rows)
                    else failed

------------------------
-- MAYBE
------------------------

maybeResult :: Choose e (Maybe ans)
maybeResult = Choose{ choose_ = operation  (\xs k ->
                                 let fun ys = case ys of
                                      []      -> return Nothing
                                      (y:ys') -> do res <- k y
                                                    case res of
                                                      Nothing -> fun ys'
                                                      _       -> return res

                                 in fun xs )}

queensMaybe :: Int -> Eff e (Maybe [Int])
queensMaybe n = handle maybeResult $
                  do ls <- queensComp n
                     return $ Just ls

------------------------
-- FIRST
------------------------

newtype Stack e a = Stack ([Eff (State (Stack e a) :* e) a])


firstResult :: Choose (State (Stack e ans) :* e) ans
firstResult = Choose { choose_ = operation (\xs k ->
                                 case xs of
                                      []     -> do Stack stack <- get
                                                   case stack of
                                                     []     -> error "no possible solutions"
                                                     (z:zs) -> do put $ Stack zs
                                                                  z
                                      (y:ys) -> do Stack zs <- get
                                                   put $ Stack (map k ys ++ zs)
                                                   k y
                                 )
                    }

handleFirst :: Eff (Choose :* (State (Stack e ans) :* e)) ans -> Eff e ans
handleFirst comp = lstate (Stack []) $
                   handle firstResult $
                   comp

queensFirst :: Int -> Eff () [Int]
queensFirst n = handleFirst $
                queensComp n


------------------------
--

pureTest       n = head $ queensPure n
maybeTest      n = erun $ queensMaybe n
firstTest      n = erun $ queensFirst n

comp n = [ bench "monad"          $ whnf pureTest n
         , bench "effect maybe"   $ whnf maybeTest n
         , bench "effect first "  $ whnf firstTest n
         ]


main :: IO ()
main = defaultMain
       [ bgroup "20" (comp 20) ]
