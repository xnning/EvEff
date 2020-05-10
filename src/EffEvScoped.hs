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
              Eff
            , (:*)
            , In, (:?)

            , Op, operation, function, value
            , handle          -- :: h e ans -> Eff (h :* e) ans -> Eff e ans
            , perform         -- :: In h e => (forall e' ans. h e' ans -> Op a b e' ans) -> a -> Eff e b
            , erun            -- :: Eff () a -> a

            , Local           -- local state
            , local
            , localGet
            , localSet
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
  LCons :: !(Marker ans) -> !(h (Loc a :* e) ans) -> !(Context e) -> Context (h :* e)
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
  return x      = Eff (\ctx -> pure x)
  Eff eff >>= f = Eff (\ctx -> do ctl <- eff ctx
                                  under ctx (f ctl))


handle :: h e ans -> Eff (h :* e) ans -> Eff e ans
handle h action
  = Eff (\ctx -> prompt $ \m ->                  -- set a fresh prompt with marker `m`
                 do under (CCons m h ctx) action) -- and call action with the extra evidence

erun :: Eff () a -> a
erun (Eff eff)  = runCtl (eff CNil)



data Loc a e ans = Loc

getLoc :: Eff (Loc a :* e) a
getLoc = undefined

setLoc :: a -> Eff (Loc a :* e) ()
setLoc x = undefined


handlerLoc :: a -> h (Loc a :* e) ans -> Eff (h :* e) ans -> Eff e ans
handlerLoc init h action
    = Eff (\ctx -> prompt $ \m ->
                   do under (LCons m h ctx) action)


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

------------------------------------
-- Operations
-------------------------------------

-- Operations of type `a -> b` in a handler context `ans`
newtype Op a b e ans = Op { getOp :: Marker ans -> Context e -> a -> Ctl b}

-- general operation with a resumption (exceptions, async/await, etc)
operation :: (a -> (b -> Eff e ans) -> Eff e ans) -> Op a b e ans
operation f = Op (\m ctx x -> Control m (\ctlk ->
                       let k y = Eff (\ctx' -> guard ctx ctx' ctlk y)
                       in under ctx (f x k)) Pure)

-- tail-resumptive operation (almost all operations)
function :: (a -> Eff e b) -> Op a b e ans
function f = Op (\_ ctx x -> under ctx (f x))

value :: b -> Op () b e ans
value x = function (\() -> return x)


-- Given evidence and an operation selector, perform the operation
perform :: In h e => (forall e' ans. h e' ans -> Op a b e' ans) -> a -> Eff e b
{-# INLINE perform #-}
perform selectOp x = Eff $ \ctx ->
  case subContext ctx of
    SubContext m h ctx -> getOp (selectOp h) m ctx x

guard :: Context e -> Context e -> (b -> Ctl a) -> b -> Ctl a
guard ctx1 ctx2 k x = if (ctx1 == ctx2) then k x
  else error "unscoped resumption"

instance Eq (Context e) where
  CNil               == CNil                = True
  (CCons m1 h1 ctx1) == (CCons m2 h2 ctx2)  = (markerEq m1 m2) && (ctx1 == ctx2)

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
