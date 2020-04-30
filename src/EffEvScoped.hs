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

module EffEvScoped(
              -- Eff,
              (:*)
            , In, (:?)

            , Op(Normal,Tail), opTail
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

            -- just for EffEvScopedOP
            , Context(..)
            , SubContext(..), withSubContext
            , under, guard
            , Eff(..)
            ) where

import Prelude hiding (read,flip)
import Control.Monad( ap, liftM )
import Data.Type.Equality( (:~:)( Refl ) )
import Ctl

import Unsafe.Coerce     (unsafeCoerce)

infixr 5 :*

-------------------------------------------------------
-- The handler context
-------------------------------------------------------
data (h :: * -> * -> *) :* e

data Context e where
  CCons :: !(Marker ans) -> !(h e ans) -> !(Context e) -> Context (h :* e)
  CNil  :: Context ()



-------------------------------------------------------
-- The Effect monad
-------------------------------------------------------
newtype Eff e a = Eff (Context e -> Ctl a)

lift :: Ctl a -> Eff e a
{-# INLINE lift #-}
lift ctl = Eff (\_ -> ctl)

under :: Context e -> Eff e a -> Ctl a
{-# INLINE under #-}
under ctx (Eff eff)  = eff ctx


instance Functor (Eff e) where
  fmap  = liftM
instance Applicative (Eff e) where
  pure  = return
  (<*>) = ap
instance Monad (Eff e) where
  return x          = Eff (\ctx -> pure x)
  (Eff eff) >>= f   = Eff (\ctx -> eff ctx >>= (\x -> under ctx (f x)))


handle :: h e ans -> Eff (h :* e) ans -> Eff e ans
handle h action
  = Eff (\ctx -> mprompt $ \m ->                  -- set a fresh prompt with marker `m`
                 do under (CCons m h ctx) action) -- and call action with the extra evidence

erun :: Eff () a -> a
erun (Eff eff)  = mrun (eff CNil)

---------------------------------------------------------
-- In, Context
---------------------------------------------------------
data SubContext h   = forall e ans. SubContext !(Marker ans) !(h e ans) !(Context e)

type h :? e = In h e

class In h e where
  subContext :: Context e -> SubContext h

instance (InEq (HEqual h h') h h' w) => In h (h' :* w)  where
  subContext = subContextEq


type family HEqual (h :: * -> * -> *) (h' :: * -> * -> *) :: Bool where
  HEqual h h  = 'True
  HEqual h h' = 'False

class (iseq ~ HEqual h h') => InEq iseq h h' e  where
  subContextEq :: Context (h' :* e) -> SubContext h

instance (h ~ h') => InEq 'True h h' e where
  subContextEq (CCons m h ctx) = SubContext m h ctx

instance ('False ~ HEqual h h', In h e) => InEq 'False h h' e where
  subContextEq (CCons m h ctx) = subContext ctx

withSubContext :: (In h e) => (SubContext h -> Ctl a) -> Eff e a
{-# INLINE withSubContext #-}
withSubContext f
  = Eff (\ctx -> f (subContext ctx))


------------------------------------------------------------------------
-- Allow giving closed type signature (like `State Int :* Amb :* ()`)
-- and later open it up in another context
------------------------------------------------------------------------

class Sub e1 e2 where
  open :: Eff e1 a -> Eff e2 a

instance Sub () e where
  open eff = Eff $ \w -> under CNil eff

instance (SubH h, Sub e1 e2) => Sub (h :* e1) (h :* e2) where
  open eff = Eff $ \(CCons m h ctx) ->
    under ctx $ open (Eff $ \subctx -> under (CCons m (subH ctx h) subctx) eff)

openOp :: (Sub e1 e2) => Context e2 -> Op a b e2 ans -> Op a b e1 ans
openOp w (Normal f) = Normal $ \a g ->
                        Eff $ \_ -> under w $ f a (\b -> open (g b))

-- openOp w (Tail f)   = Tail $ \a ->
--                        Eff $ \_ -> under w (f a)

class SubH h where
  subH :: Sub e1 e2  => Context e2 -> h e2 a -> h e1 a



------------------------------------
-- Operations
-------------------------------------

-- Operations of type `a -> b` in a handler context `ans`
data Op a b e ans = Tail   !(Context e -> a -> Ctl b)                       -- tail-resumptive operation (almost all operations)
                  | Normal !(a -> (b -> Eff e ans) -> Eff e ans) -- general operation with a resumption (exceptions, async/await, etc)




-- Given evidence and an operation selector, perform the operation
-- perform :: In h e => (forall e' ans. Handler h e' ans -> Clause a b e' ans) -> a -> Eff e b
perform :: h :? e => (forall e' ans. h e' ans -> Op a b e' ans) -> a -> Eff e b
{-# INLINE perform #-}
perform selectOp x
  = withSubContext $ \(SubContext m h ctx) ->
    case selectOp h of
      Tail tailop -> tailop ctx x             -- great! directly execute in place without capturing the continuation.
      Normal op   -> mcontrol m $ \ctlk ->    -- yield up to the handler/prompt m in some context of type `::ans`
                     let k y = Eff (\ctx' -> guard ctx ctx' ctlk y)
                     in under ctx (op x k)

guard :: Context e -> Context e -> (b -> Ctl a) -> b -> Ctl a
guard ctx1 ctx2 k x = if (ctx1 == ctx2) then k x else error "unscoped resumption"

instance Eq (Context e) where
  CNil               == CNil                = True
  (CCons m1 h1 ctx1) == (CCons m2 h2 ctx2)  = (markerEq m1 m2) && (ctx1 == ctx2)


opTail :: (a -> Eff e b) -> Op a b e ans
opTail f = Tail (\ctx x -> under ctx (f x))

------------------------------------
-- Local state
-------------------------------------
local :: a -> (Local a -> Eff e b) -> Eff e b
{-# INLINE local #-}
local init action = Eff (\w -> mlocal init (\l -> under w (action l)))

{-# INLINE localGet #-}
localGet :: Local a -> b -> Eff e a
localGet l x = Eff (\_ -> (mlocalGet l x))

{-# INLINE localSet #-}
localSet :: Local a -> a -> Eff e ()
localSet l x = lift (mlocalSet l x)
