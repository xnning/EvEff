-----------------------------------------------------
-- Copyright 2020, Daan Leijen, Ningning Xie.
-----------------------------------------------------
{-# LANGUAGE  TypeOperators,            -- h :* e                     (looks nice but not required)
              ConstraintKinds,          -- type (h ?: e) = In h e     (looks nice but not required)
              FlexibleInstances,        -- instance Sub () e          (non type variable in head)
              FlexibleContexts,         -- (State Int ?: e) => ...    (non type variable argument)
              DataKinds, TypeFamilies,  -- type family HEqual h h' :: Bool
              UndecidableInstances,     -- InEq (HEqual h h') h h' e => ... (duplicate instance variable)
              GADTs,
              MultiParamTypeClasses,
              Rank2Types
#-}

module EffEvScopedOP(
              Eff, (:*)
            , In, (:?)

            , Op, function, operation, value
            , handle          -- :: h e ans -> Eff (h :* e) ans -> Eff e ans
            , perform         -- :: In h e => (forall e' ans. h e' ans -> Op a b e' ans) -> a -> Eff e b
            , erun            -- :: Eff () a -> a

            , Sub, SubH(..)
            , open            -- :: Sub e1 e2 => Eff e1 a -> Eff e2 a
            , openOp

            , Local           -- local state
            , local
            , localGet
            , localSet

            ) where

import Ctl

import EffEvScoped hiding (Op, opTail, perform)

------------------------------------
-- Operations
-------------------------------------

-- Operations of type `a -> b` in a handler context `ans`
newtype Op a b e ans = Op { getOp :: Marker ans -> Context e -> a -> Ctl b}

-- Given evidence and an operation selector, perform the operation
-- perform :: In h e => (forall e' ans. Handler h e' ans -> Clause a b e' ans) -> a -> Eff e b
perform :: In h e => (forall e' ans. h e' ans -> Op a b e' ans) -> a -> Eff e b
{-# INLINE perform #-}
perform selectOp x = Eff $ \ctx ->
  case subContext ctx of
    SubContext m h ctx -> getOp (selectOp h) m ctx x

-- tail-resumptive operation (almost all operations)
function :: (a -> Eff e b) -> Op a b e ans
function f = Op (\_ ctx x -> under ctx (f x))

value :: b -> Op () b e ans
value x = function (\() -> return x)

-- general operation with a resumption (exceptions, async/await, etc)
operation :: (a -> (b -> Eff e ans) -> Eff e ans) -> Op a b e ans
operation f = Op (\m ctx x -> Control m (\ctlk ->
                       let k y = Eff (\ctx' -> guard ctx ctx' ctlk y)
                       in under ctx (f x k)) Pure)
