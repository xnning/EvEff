{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators, ScopedTypeVariables #-}

module TestAOP where

import Prelude hiding (log, exp)
import Data.Map hiding (lookup,map)

import System.Random
import Criterion.Main
import Criterion.Types


-- Mtl
import Control.Monad.State
import Control.Monad.Writer
import Control.Monad.Identity
import Control.Applicative hiding (empty)
import Control.Monad.Except

-- Extensible Effects
import qualified Control.Eff as EE
import qualified Control.Eff.State.Strict as EEs
import qualified Control.Eff.Writer.Strict as EEw

-- Fused Effects
import qualified Control.Algebra as F
import qualified Control.Carrier.State.Strict as Fs
import qualified Control.Carrier.Writer.Strict as Fw

-- Eff
import Control.Ev.Eff
import qualified Control.Ev.Util as E

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
     --tell (show s ++ "\n")
     --tell ("Entering eval with " ++ show exp ++ "\n")
     tell ("enter: " ++ show (length s))
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
     -- tell ("Exiting eval with " ++ show result ++ "\n")
     tell "exit"
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
  -- tell ("Entering " ++ name ++ " with " ++ show x ++ "\n")
  -- tell "enter"
  y <- super x
  -- tell ("Exiting " ++ name ++ " with " ++ show y ++ "\n")
  tell "exit"
  return y

-- the environment dumping mixin
dump :: (MonadState [s] m, MonadWriter String m, Show s) => Open (a -> m b)
dump super arg = do  s <- get
                     tell ("enter: " ++ show (length s))
                     super arg

compMixin = new (dump <@> log "eval"  <@> evalMixin)
testEvalMixin e = evalState (execWriterT (compMixin e)) []

---------------------------------------------------------
-- Extensible Effects
---------------------------------------------------------

evalEE :: (EE.Member (EEs.State Env) r, EE.Member (EEw.Writer String) r) => Expr -> EE.Eff r Int
evalEE exp =
  do (s::Env) <- EEs.get
     --tell (show s ++ "\n")
     --tell ("Entering eval with " ++ show exp ++ "\n")
     EEw.tell ("enter: " ++ show (length s))
     result <-
       case exp of
         Lit x             -> return x
         Var s             -> do  e <- EEs.get
                                  case lookup s e of
                                    Just x  -> return x
                                    _       -> error "Variable not found!"
         Plus l r          -> do  x <- evalEE l
                                  y <- evalEE r
                                  return (x+y)
         Assign x r        -> do  y <- evalEE r
                                  e <- EEs.get
                                  EEs.put ((x,y):e)
                                  return y
         Sequence []       -> return 0
         Sequence [x]      -> evalEE x
         Sequence (x:xs)   -> evalEE x >> evalEE (Sequence xs)
         While c b         -> do  x <- evalEE c
                                  if (x == 0) then return 0
                                    else (evalEE b >> evalEE exp)
     -- tell ("Exiting eval with " ++ show result ++ "\n")
     EEw.tell "exit"
     return result

testEvalEE :: Expr -> String -- ((Int,Env),String
testEvalEE e = snd (EE.run $ EEw.runMonoidWriter (EEs.runState ([]::Env) (evalEE e)))

---------------------------------------------------------
-- Extensible
---------------------------------------------------------

evalF :: (F.Has (Fs.State Env) sig m, F.Has (Fw.Writer String) sig m) => Expr -> m Int
evalF exp =
  do (s::Env) <- Fs.get
     --tell (show s ++ "\n")
     --tell ("Entering eval with " ++ show exp ++ "\n")
     Fw.tell ("enter: " ++ show (length s))
     result <-
       case exp of
         Lit x             -> return x
         Var s             -> do  e <- Fs.get
                                  case lookup s e of
                                    Just x  -> return x
                                    _       -> error "Variable not found!"
         Plus l r          -> do  x <- evalF l
                                  y <- evalF r
                                  return (x+y)
         Assign x r        -> do  y <- evalF r
                                  e <- Fs.get
                                  Fs.put ((x,y):e)
                                  return y
         Sequence []       -> return 0
         Sequence [x]      -> evalF x
         Sequence (x:xs)   -> evalF x >> evalF (Sequence xs)
         While c b         -> do  x <- evalF c
                                  if (x == 0) then return 0
                                    else (evalF b >> evalF exp)
     -- tell ("Exiting eval with " ++ show result ++ "\n")
     Fw.tell "exit"
     return result

testEvalF :: Expr -> String -- (String, (Env, Int))
testEvalF e = fst (F.run $ Fw.runWriter (Fs.runState ([]::Env) (evalF e)))

---------------------------------------------------------
-- Eff
---------------------------------------------------------

evalEff ::  (E.Writer String :? e, (E.State Env) :? e) => Expr -> Eff e Int
evalEff exp =
  do (s::Env) <- perform E.get ()
     --perform E.tell (show s ++ "\n")
     --perform E.tell ("Entering eval with " ++ show exp ++ "\n")
     perform E.tell ("enter: " ++ show (length s))
     result <-
       case exp of
         Lit x             -> return x
         Var s             -> do  e <- perform E.get ()
                                  case lookup s e of
                                    Just x  -> return x
                                    _       -> error "Variable not found!"
         Plus l r          -> do  x <- evalEff l
                                  y <- evalEff r
                                  return (x+y)
         Assign x r        -> do  y <- evalEff r
                                  e <- perform E.get ()
                                  perform E.put ((x,y):e)
                                  return y
         Sequence []       -> return 0
         Sequence [x]      -> evalEff x
         Sequence (x:xs)   -> evalEff x >> evalEff (Sequence xs)
         While c b         -> do  x <- evalEff c
                                  if (x == 0) then return 0
                                    else (evalEff b >> evalEff exp)
     -- perform E.tell ("Exiting eval with " ++ show result ++ "\n")
     perform E.tell "exit"
     return result

handleEff ::  Expr -> Eff e (Int, String)
handleEff e = E.writer $
              E.state ([]::Env) $
              do x <- evalEff e
                 return $ x

testEvalEff e = snd (runEff (handleEff e))

---------------------------------------------------------
-- ALGEBRAIC NON TAIL
---------------------------------------------------------
stateNonTail :: a -> Eff (E.State a :* e) ans -> Eff e ans
stateNonTail init
  = handlerLocal init (E.State{ E.get = operation (\() k -> do{ x <- localGet; k x }),
                                E.put = operation (\x k  -> do{ localPut x; k () }) })

handleEffNonTail ::  Expr -> Eff e (Int,String)
handleEffNonTail e = E.writer $
                     stateNonTail ([]::Env) $
                     do x <- evalEff e
                        return $ x

testEvalEffNonTail e = snd (runEff (handleEffNonTail e))

{-
---------------------------------------------------------
-- Linear
---------------------------------------------------------

evalEffL ::  (Linear (E.Writer String) :? e, Linear (E.State Env) :? e) => Expr -> Eff e Int
evalEffL exp =
  do (s::Env) <- lperform E.get ()
     -- perform E.tell (show s ++ "\n")
     -- perform E.tell ("Entering eval with " ++ show exp ++ "\n")
     lperform E.tell ("enter: " ++ show (length s))
     result <-
       case exp of
         Lit x             -> return x
         Var s             -> do  e <- lperform E.get ()
                                  case lookup s e of
                                    Just x  -> return x
                                    _       -> error "Variable not found!"
         Plus l r          -> do  x <- evalEffL l
                                  y <- evalEffL r
                                  return (x+y)
         Assign x r        -> do  y <- evalEffL r
                                  e <- lperform E.get ()
                                  lperform E.put ((x,y):e)
                                  return y
         Sequence []       -> return 0
         Sequence [x]      -> evalEffL x
         Sequence (x:xs)   -> evalEffL x >> evalEffL (Sequence xs)
         While c b         -> do  x <- evalEffL c
                                  if (x == 0) then return 0
                                    else (evalEffL b >> evalEffL exp)
     -- perform E.tell ("Exiting eval with " ++ show result ++ "\n")
     lperform E.tell "exit"
     return result

handleEffL ::  Expr -> Eff e (Int, String)
handleEffL e = E.lwriter $
               E.lstate ([]::Env) $
               do x <- evalEffL e
                  return $ x

testEvalEffL e = snd (runEff (handleEffL e))
-}

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
randomExpr 1 = do i <- getStdRandom (randomR(1, n-1))
                  if (i`mod`3 == 0) then return (Var "x")
                     else (do n <- randomLit
                              return $ Lit n)
randomExpr n = do i <- getStdRandom (randomR(1, n-1))
                  l <- randomExpr i
                  r <- randomExpr (n-i)
                  return $ if (i`mod`10 == 0) then Sequence [Assign "x" l, r] else Plus l r

makeGroup n =
  do e0 <- randomExpr n
     let e = Sequence [Assign "x" (Lit 0), e0]
     return $ [ bgroup (show n)  [ bench "monad"     $ whnf last (testEvalMonad e)
                                 , bench "mixin"     $ whnf last (testEvalMixin e)
                                 , bench "extensible" $ whnf last (testEvalEE e)
                                 , bench "fused"      $ whnf last (testEvalF e)
                                 -- , bench "eff linear" $ whnf last (testEvalEffL e)
                                 , bench "eff"          $ whnf last (testEvalEff e)
                                 , bench "eff non tail" $ whnf last (testEvalEffNonTail e)
                                 ]
              ]

seed = 42
n = 12::Int

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
