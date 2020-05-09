{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators, ScopedTypeVariables #-}

module TestAOP where

import Prelude hiding (log, exp)
import Control.Monad.State
import Control.Monad.Writer
import Control.Monad.Identity
import Control.Applicative hiding (empty)
import Control.Monad.Except
import Data.Map hiding (lookup,map)


import System.Random
import Criterion.Main
import Criterion.Types

import EffEvScoped
import qualified Library as E

data Expr
  = Lit Int
  | Var String
  | Plus Expr Expr
  | Assign String Expr
  | Sequence [Expr]
  | While Expr Expr
  deriving Show

type Env = [(String, Int)]

evalMonad :: Expr -> StateT Env (Writer String) Int
evalMonad exp =
  do s <- get
     tell (show s ++ "\n")
     tell ("Entering eval with " ++ show exp ++ "\n")
     result <-
       case exp of
         Lit x             -> return x
         Var s             -> do  e <- get
                                  case lookup s e of
                                    Just x  -> return x
                                    _       -> error "Variable not found!"
         Plus l r          -> do  x <- evalMonad l
                                  y <- evalMonad r
                                  return (x+y)
         Assign x r        -> do  y <- evalMonad r
                                  e <- get
                                  put ((x,y):e)
                                  return y
         Sequence []       -> return 0
         Sequence [x]      -> evalMonad x
         Sequence (x:xs)   -> evalMonad x >> evalMonad (Sequence xs)
         While c b         -> do  x <- evalMonad c
                                  if (x == 0) then return 0
                                    else (evalMonad b >> evalMonad exp)
     tell ("Exiting eval with " ++ show result ++ "\n")
     return result

testEvalMonad e = execWriter (runStateT (evalMonad e) [])

---------------------------------------------------------
-- MIXIN
---------------------------------------------------------

type Open s = s -> s

new :: Open s -> s
new a = let this = a this in this

zero :: Open s
zero = id

(<@>) :: Open s -> Open s -> Open s
a1 <@> a2  = \super -> a1 (a2 super)

evalMixin :: MonadState Env m => Open (Expr -> m Int)
evalMixin this exp = case exp of
  Lit x             -> return x
  Var s             -> do  e <- get
                           case lookup s e of
                             Just x  -> return x
                             _       -> error msg
  Plus l r          -> do  x <- this l
                           y <- this r
                           return (x+y)
  Assign x r        -> do  y <- this r
                           e <- get
                           put ((x,y):e)
                           return y
  Sequence []       -> return 0
  Sequence [x]      -> this x
  Sequence (x:xs)   -> this x >> this (Sequence xs)
  While c b         -> do  x <- this c
                           if (x == 0) then return 0
                             else (this b >> this exp)
  where msg = "Variable not found!"

-- the logging mixin
log :: (MonadWriter String m, Show a, Show b) => String -> Open (a -> m b)
log name super x =  do
  tell ("Entering " ++ name ++ " with " ++ show x ++ "\n")
  y <- super x
  tell ("Exiting " ++ name ++ " with " ++ show y ++ "\n")
  return y

-- the environment dumping mixin
dump :: (MonadState s m, MonadWriter String m, Show s) => Open (a -> m b)
dump super arg = do  s <- get
                     tell (show s ++ "\n")
                     super arg

compMixin = new (dump <@> log "eval"  <@> evalMixin)
testEvalMixin e = evalState (execWriterT (compMixin e)) []

---------------------------------------------------------
-- ALGEBRAIC
---------------------------------------------------------

evalEff ::  (E.Writer String :? e, E.State Env :? e) => Expr -> Eff e Int
evalEff exp =
  do (s::Env) <- E.get
     E.tell (show s ++ "\n")
     E.tell ("Entering eval with " ++ show exp ++ "\n")
     result <-
       case exp of
         Lit x             -> return x
         Var s             -> do  e <- E.get
                                  case lookup s e of
                                    Just x  -> return x
                                    _       -> error "Variable not found!"
         Plus l r          -> do  x <- evalEff l
                                  y <- evalEff r
                                  return (x+y)
         Assign x r        -> do  y <- evalEff r
                                  e <- E.get
                                  E.put ((x,y):e)
                                  return y
         Sequence []       -> return 0
         Sequence [x]      -> evalEff x
         Sequence (x:xs)   -> evalEff x >> evalEff (Sequence xs)
         While c b         -> do  x <- evalEff c
                                  if (x == 0) then return 0
                                    else (evalEff b >> evalEff exp)
     E.tell ("Exiting eval with " ++ show result ++ "\n")
     return result

handleEff ::  Expr -> Eff e (String, Int)
handleEff e = E.writer "" $
            E.lstate ([]::Env) $
            do x <- evalEff e
               return $ x

testEvalEff e = fst (erun (handleEff e))

---------------------------------------------------------
-- ALGEBRAIC NON TAIL
---------------------------------------------------------

handleEffNonTail ::  Expr -> Eff e (String, Int)
handleEffNonTail e = E.writerNonTail "" $
                   E.lstateNonTail ([]::Env) $
                   do x <- evalEff e
                      return $ x

testEvalEffNonTail e = fst (erun (handleEffNonTail e))

---------------------------------------------------------
-- TEST
---------------------------------------------------------

randomLit :: IO Int
randomLit = getStdRandom (randomR(0, (2^16)-1))

randomBool :: IO Bool
randomBool = getStdRandom random

-- Generate a random expression tree of size n, consisting only of
-- Plus nodes and Lit leaves.
randomExpr :: Int -> IO Expr
randomExpr 1 = do n <- randomLit
                  return $ Lit n
randomExpr n = do i <- getStdRandom (randomR(1, n-1))
                  l <- randomExpr i
                  r <- randomExpr (n-i)
                  return $ Plus l r

makeGroup n =
  do e <- randomExpr n
     return $ [ bgroup (show n)  [ bench "monad"     $ whnf last (testEvalMonad e)
                                 , bench "mixin"     $ whnf last (testEvalMixin e)
                                 , bench "algebraic" $ whnf last (testEvalEff e)
                                 , bench "algebraic non tail" $ whnf last (testEvalEffNonTail e)
                                 ]
              ]

seed = 42
n = 10

main = do setStdGen (mkStdGen seed);
          e <- makeGroup (2^n)
          defaultMain e

expr = Plus (Lit 1) (Lit 2)

test = do putStr "============== monad =============\n"
          putStr $ testEvalMonad expr
          putStr "============== mixin =============\n"
          putStr $ testEvalMixin expr
          putStr "============== effect ============\n"
          putStr $ testEvalEff expr
