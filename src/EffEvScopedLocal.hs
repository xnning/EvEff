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

module EffEvScopedLocal(
              -- Eff,
              (:*)
            , In, (:?)

            , Op
            , function
            , operation
            , handler         -- :: h e ans -> Eff (h :* e) ans -> Eff e ans

            , perform         -- :: In h e => (forall e' ans. h e' ans -> Op a b e' ans) -> a -> Eff e b
            , erun            -- :: Eff () a -> a

            , Sub, SubH(..)
            , open            -- :: Sub e1 e2 => Eff e1 a -> Eff e2 a
            -- , openOp

            , Loc
            , getLoc
            , setLoc
            , handlerLoc
            , handlerLocRet

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
import Data.IORef

-- import Unsafe.Coerce     (unsafeCoerce)

infixr 5 :*

-------------------------------------------------------
-- The handler context
-------------------------------------------------------
data (h :: * -> * -> *) :* e

data Context e where
  CCons :: !(Marker ans) -> !(h e ans) -> !(Context e) -> Context (h :* e)
  LCons :: !(Marker ans) -> !(Loc a e ans) -> !(h (Loc a :* e) ans) -> !(Context e) -> Context (h :* e)
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


handler :: h e ans -> Eff (h :* e) ans -> Eff e ans
handler h action
  = Eff (\ctx -> mprompt $ \m ->                  -- set a fresh prompt with marker `m`
                 do under (CCons m h ctx) action) -- and call action with the extra evidence

erun :: Eff () a -> a
erun (Eff eff)  = mrun (eff CNil)

handlerRet f h action
  = handler h (do x <- action; return (f x))



newtype Loc a e ans = Loc (IORef a)

getLoc :: Eff (Loc a :* e) a
getLoc = Eff (\(CCons _ (Loc r) _) -> ctlIO (readIORef r))

setLoc :: a -> Eff (Loc a :* e) ()
setLoc x = Eff (\(CCons _ (Loc r) _) -> ctlIO (writeIORef r x))


handlerLocRet :: a -> (ans -> a -> b) -> h (Loc a :* e) ans -> Eff (h :* e) ans -> Eff e b
handlerLocRet init ret h action
    = Eff (\ctx -> do r <- ctlIO (newIORef init)
                      x <- mprompt $ \m -> under (LCons m (Loc r) h ctx) action
                      y <- ctlIO (readIORef r)
                      return (ret x y))

handlerLoc init h action
  = handlerLocRet init const h action


---------------------------------------------------------
-- In, Context
---------------------------------------------------------
data SubContext h   = forall e ans. SubContext !(Marker ans) !(h e ans) !(Context e)
                    | forall a e ans. SubContextLoc !(Marker ans) !(Loc a e ans) !(h (Loc a :* e) ans) !(Context e)

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
  subContextEq (LCons m l h ctx) = SubContextLoc m l h ctx

instance ('False ~ HEqual h h', In h e) => InEq 'False h h' e where
  subContextEq (CCons m h ctx) = subContext ctx
  subContextEq (LCons m l h ctx) = subContext ctx

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

{-
openOp :: (Sub e1 e2) => Context e2 -> Op a b e2 ans -> Op a b e1 ans
openOp w (Op f) = Op $ \a g ->
                  Eff $ \_ -> under w $ f a (\b -> open (g b))
-}
-- openOp w (Tail f)   = Tail $ \a ->
--                        Eff $ \_ -> under w (f a)

class SubH h where
  subH :: Sub e1 e2  => Context e2 -> h e2 a -> h e1 a



------------------------------------
-- Operations
-------------------------------------
-- Operations of type `a -> b` in a handler context `ans`
newtype Op a b e ans = Op { getOp :: Marker ans -> Context e -> a -> Ctl b}

-- Given evidence and an operation selector, perform the operation
-- perform :: In h e => (forall e' ans. Handler h e' ans -> Clause a b e' ans) -> a -> Eff e b
perform :: In h e => (forall e' ans. h e' ans -> Op a b e' ans) -> a -> Eff e b
{-# INLINE perform #-}
perform selectOp x
  = withSubContext $ \ctx ->
    case ctx of
      SubContext m h ctx      -> getOp (selectOp h) m ctx x
      SubContextLoc m l h ctx -> getOp (selectOp h) m (CCons m l ctx) x

-- tail-resumptive operation (almost all operations)
function :: (a -> Eff e b) -> Op a b e ans
function f = Op (\_ ctx x -> under ctx (f x))

-- general operation with a resumption (exceptions, async/await, etc)
operation :: (a -> (b -> Eff e ans) -> Eff e ans) -> Op a b e ans
operation f = Op (\m ctx x -> mcontrol m $ \ctlk ->
                       let k y = Eff (\ctx' -> guard ctx ctx' ctlk y)
                       in under ctx (f x k))


guard :: Context e -> Context e -> (b -> Ctl a) -> b -> Ctl a
guard ctx1 ctx2 k x = if (ctx1 == ctx2) then k x else error "unscoped resumption"

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
