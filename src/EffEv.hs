-----------------------------------------------------
-- Copyright 2020, Daan Leijen, Ningning Xie
-----------------------------------------------------
{-# LANGUAGE  TypeOperators,            -- h :* e                     (looks nice but not required)
              ConstraintKinds,          -- type (h ?: e) = In h e     (looks nice but not required)
              FlexibleInstances,        -- instance Sub () e          (non type variable in head)
              FlexibleContexts,         -- (State Int ?: e) => ...    (non type variable argument)
              DataKinds, TypeFamilies,  -- type family HEqual h h' :: Bool
              UndecidableInstances,     -- InEq (HEqual h h') h h' e => ... (duplicate instance variable)
              ScopedTypeVariables,
              GADTs,
              MultiParamTypeClasses,
              Rank2Types
#-}
module EffEv( Eff, (:*)
            , In, (:?)

            , Op(Normal,Tail)
            , handle          -- :: h e ans -> Eff (h :* e) ans -> Eff e ans
            , perform         -- :: In h e => (forall e' ans. h e' ans -> Op a b e' ans) -> a -> Eff e b
            , erun            -- :: Eff () a -> a

            , Sub
            , open            -- :: Sub e1 e2 => Eff e1 a -> Eff e2 a

            , Local           -- local state
            , local
            , localGet
            , localSet

            ) where

import Prelude hiding (read,flip)
import Control.Monad( ap, liftM )
import Data.Type.Equality( (:~:)( Refl ) )


-------------------------------------------------------
-- Assume some way to generate a fresh prompt marker
-- associated with specific effect and answer type.
-------------------------------------------------------
import Unsafe.Coerce     (unsafeCoerce)
import System.IO.Unsafe ( unsafePerformIO )
import Data.IORef

-- an abstract marker
data Marker e a = Marker !Integer

instance Show (Marker e a) where
  show (Marker i) = show i

-- if markers match, their types are the same
match :: Marker e a -> Marker e' b -> Maybe ((a, e) :~: (b, e'))
match (Marker i) (Marker j) | i == j  = Just (unsafeCoerce Refl)
match _ _ = Nothing

unique :: IORef Integer
unique = unsafePerformIO (newIORef 0)

-- evaluate a action with a fresh marker
freshMarker :: (Marker e a -> Eff e a) -> Eff e a
freshMarker f
  = let m = unsafePerformIO $
            do i <- readIORef unique;
               writeIORef unique (i+1);
               return i
    in seq m (f (Marker m))

-------------------------------------------------------
-- The handler context
-------------------------------------------------------
infixr 5 :*

data (h :: * -> * -> *) :* e

data Context e where
  CCons :: Marker e ans -> h e ans -> Context e -> Context (h :* e)
  CNil  :: Context ()


-------------------------------------------------------
-- The Multi Prompt control monad
-- ans: the answer type, i.e. the type of the handler/prompt context.
-- e' : the answer effect, i.e. the effect in the handler/prompt context.
-- b  : the result type of the operation
-------------------------------------------------------
data Ctl e a = Pure { result :: !a }
             | forall b e' ans.
               Control{ marker :: Marker e' ans,                    -- prompt marker to yield to (in type context `::ans`)
                        op     :: (b -> Eff e' ans) -> Eff e' ans,  -- the final action, just needs the resumption (:: b -> EFf e' ans) to be evaluated.
                        cont   :: b -> Eff e a }                    -- the (partially) build up resumption; (b -> Eff e a) :~: (b -> Eff e' ans)` by the time we reach the prompt


newtype Eff e a = Eff { unEff :: Context e -> Ctl e a }


instance Functor (Eff e) where
  fmap  = liftM
instance Applicative (Eff e) where
  pure  = return
  (<*>) = ap
instance Monad (Eff e) where
  return x   = Eff (\evv -> Pure x)
  (>>=)      = bind

-- start yielding (with an initially empty continuation)
mcontrol :: Marker e ans -> ((b -> Eff e ans) -> Eff e ans) -> Eff e' b
mcontrol m op  = Eff (\ctx -> Control m op pure)

kcompose :: (b -> Eff e c) -> (a -> Eff e b) -> a -> Eff e c      -- Kleisli composition
kcompose g f x =
  case f x of
    -- bind (f x) g
    Eff eff -> Eff (\ctx -> case eff ctx of
                              Pure x -> unEff (g x) ctx
                              Control m op cont -> Control m op (g `kcompose` cont))

{-# INLINE bind #-}
bind :: Eff e a -> (a -> Eff e b) -> Eff e b
bind (Eff eff) f
  = Eff (\ctx -> case eff ctx of
                   Pure x            -> unEff (f x) ctx
                   Control m op cont -> Control m op (f `kcompose` cont))  -- keep yielding with an extended continuation




-- use a prompt with a unique marker (and handle yields to it)
prompt :: Marker e ans -> h e ans -> Eff (h :* e) ans -> Eff e ans
prompt m h (Eff eff) = Eff $ \ctx ->
  case (eff (CCons m h ctx)) of                    -- add handler o the context
    Pure x -> Pure x
    Control n op cont ->
        let cont' x = prompt m h (cont x) in      -- extend the continuation with our own prompt
        case match m n of
          Nothing   -> Control n op cont'          -- keep yielding (but with the extended continuation)
          Just Refl -> unEff (op cont') ctx   -- found our prompt, invoke `op` (under the context `ctx`).
                              -- Note: `Refl` proves `a ~ ans` and `e ~ e'` (the existential `ans,e'` in Control)

handle :: h e ans -> Eff (h :* e) ans -> Eff e ans
handle h action
  = freshMarker $ \m -> prompt m h action

-- Run a control monad
erun :: Eff () a -> a
erun (Eff eff) = case eff CNil of
                   Pure x -> x
                   Control _ _ _ -> error "Unhandled operation"  -- can never happen



reflect :: Eff e a -> Eff e (Ctl e a)
reflect (Eff eff) = Eff (\ctx -> let ctl = eff ctx in seq ctl (Pure ctl))

{-# INLINE lift #-}
lift :: Ctl e a -> Eff e a
lift ctl = Eff (\ctx -> ctl)


---------------------------------------------------------
--
---------------------------------------------------------
data SubContext h = forall e ans. SubContext !(Marker e ans) !(h e ans) !(Context e)

type h :? e = In h e

class In h e where
  subContext :: Context e -> SubContext h

instance (InEq (HEqual h h') h h' ctx) => In h (h' :* ctx)  where
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


{-# INLINE withSubContext #-}
withSubContext :: (h :? e) => (SubContext h -> Eff e a) -> Eff e a
withSubContext action
  = do ctx <- Eff Pure
       action (subContext ctx)


------------------------------------
--
-------------------------------------

-- Operations of type `a -> b` in a handler context `ans`
data Op a b e ans = Normal !(a -> (b -> Eff e ans) -> Eff e ans) -- general operation with a resumption (exceptions, async/await, etc)
                  | Tail   !(a -> Eff e b)                       -- tail-resumptive operation (almost all operations)



resumeUnder :: forall h a b e e' ans. In h e => Marker e' ans -> h e' ans -> Context e' -> (b -> Eff e' a) -> (b -> Eff e a)
resumeUnder m h ctx cont x
  = withSubContext $ \(SubContext m' h' ctx' :: SubContext h) ->
    case match m m' of
      Just Refl -> under m h ctx' (cont x)
      Nothing   -> error "EffEv.resumeUnder: marker does not match anymore (this should never happen?)"

{-# INLINE under #-}
under :: In h e => Marker e' ans -> h e' ans -> Context e' -> Eff e' b -> Eff e b
under m h ctx (Eff eff) = Eff (\_ -> case eff ctx of
                                       Pure x -> Pure x
                                       Control n op cont -> Control n op (resumeUnder m h ctx cont))

-- Given evidence and an operation selector, perform the operation
{-# INLINE perform #-}
perform :: In h e => (forall e' ans. h e' ans -> Op a b e' ans) -> a -> Eff e b
perform selectOp x
  = withSubContext $ \(SubContext m h ctx) ->
    case selectOp h of
      Tail tailop -> under m h ctx (tailop x)    -- great! directly execute in place without capturing the continuation.
      Normal op   -> mcontrol m (op x)


------------------------------------
-- Local state
-------------------------------------
newtype Local a = Local (IORef a)

{-# INLINE unsafeIO #-} 
unsafeIO :: IO a -> Eff e a
unsafeIO io = let x = unsafePerformIO io in seq x (lift (Pure x))

{-# INLINE localGet #-}
localGet :: Local a -> Eff e a
localGet (Local r) = unsafeIO (readIORef r)

{-# INLINE localSet #-}
localSet :: Local a -> a -> Eff e ()
localSet (Local r) x = unsafeIO (writeIORef r x)

localOutOfScope :: Local a -> Eff e a
localOutOfScope local
  = do x <- localGet local
       localSet local (error "local state is accessed outside its scope")
       return x

local :: a -> (Local a -> Eff e b) -> Eff e b
local init action
  = do ref <- unsafeIO (newIORef init)
       let local = Local ref
       plocal local (action local)

plocal :: Local a -> Eff e b -> Eff e b
plocal local action
  = do ctl <- reflect action
       case ctl of
         Pure x -> do localOutOfScope local
                      return x
         Control m op cont
           -> do val <- localOutOfScope local           -- save current value
                 let cont' x = do localSet local val    -- restore saved value on resume
                                  plocal local (cont x)
                 lift (Control m op cont')


------------------------------------------------------------------------
-- Allow giving closed type signature (like `State Int :* Amb :* ()`)
-- and later open it up in another context
------------------------------------------------------------------------

open :: Sub e1 e2 => Eff e1 a -> Eff e2 a
open eff = unsafeCoerce eff

class Sub e1 e2 where
instance Sub () e
instance Sub e1 e2 => Sub (h :* e1) (h :* e2)
