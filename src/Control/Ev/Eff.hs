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
{-|
Description : Efficient effect handlers based on Evidence translation
Copyright   : (c) 2020, Microsoft Research; Daan Leijen; Ningning Xie
License     : MIT
Maintainer  : xnning@hku.hk; daan@microsoft.com
Stability   : Experimental

Efficient effect handlers based on Evidence translation. The implementation
is based on /"Effect Handlers, Evidently"/, Ningning Xie /et al./, ICFP 2020.

Example:

@
-- A @Reader@ effect definition with one operation @ask@ of type @()@ to @a@.
data Reader a e ans = Reader{ ask :: Op () a e ans }

greet :: (Reader String :? e) => Eff e String
greet = do s <- perform ask ()
           return ("hello " ++ s)

test :: String
test = runEff $
       handler (Reader{ ask = value "world" }) $  -- @:: Reader String () Int@
       do s <- greet                              -- executes in context @:: Eff (Reader String :* ()) Int@
          return (length s)
@

Note: to use this library, you generally need:

@
\{\-\# LANGUAGE  TypeOperators, FlexibleContexts, Rank2Types  \#\-\}
@

in front of your module declaration.

Enjoy,
  Daan Leijen and Ningning Xie,  May 2020.
-}
module Control.Ev.Eff(
            -- * Effect monad
              Eff
            , runEff          -- :: Eff () a -> a

            -- * Effect context
            , (:?)            -- h :? e
            , (:*)            -- h :* e
            -- , In              -- alias for :?

            -- * Perform and Handlers
            , perform         -- :: (h :? e) => (forall e' ans. h e' ans -> Op a b e' ans) -> a -> Eff e b
            , handler         -- :: h e ans -> Eff (h :* e) ans -> Eff e ans
            , handlerRet      -- :: (ans -> b) -> h e b -> Eff (h :* e) ans -> Eff e b
            , handlerHide     -- :: h (h' :* e) ans -> Eff (h :* e) ans -> Eff (h' :* e) ans
            , mask            -- :: Eff e ans -> Eff (h :* e) ans

            -- ** Defining operations
            , Op
            , value           -- :: a -> Op () a e ans
            , function        -- :: (a -> Eff e b) -> Op a b e ans
            , except          -- :: (a -> Eff e ans) -> Op a b e ans
            , operation       -- :: (a -> (b -> Eff e ans)) -> Op a b e ans

            -- * Local state
            , Local           -- Local a e ans

            , local           -- :: a -> Eff (Local a :* e) ans -> Eff e ans
            , handlerLocal    -- :: a -> h (Local a :* e) ans -> Eff (h :* e) ans -> Eff e ans
            , handlerLocalRet -- :: a -> (ans -> a -> b) -> h (Local a :* e) b -> Eff (h :* e) ans -> Eff e b

            , lget            -- :: (Local a :? e) => Eff e a
            , lput            -- :: (Local a :? e) => a -> Eff e ()
            , lupdate         -- :: (Local a :? e) => (a -> a) -> Eff e ()

            , localGet        -- :: Eff (Local a :* e) a
            , localPut        -- :: a -> Eff (Local a :* e) ()
            , localUpdate     -- :: (a -> a) -> Eff (Local a :* e) a

            ) where

import Prelude hiding (read,flip)
import Control.Monad( ap, liftM )
import Data.Type.Equality( (:~:)( Refl ) )
import Control.Ev.Ctl hiding (Local)
import Data.IORef

-- import Unsafe.Coerce     (unsafeCoerce)

infixr 5 :*

-------------------------------------------------------
-- The handler context
-------------------------------------------------------

-- | An effect context is a type-level list of effects.
-- An effect context always has the form @(h1 :* h2 :* ... :* hn :* ())@ where
-- operations in @h1@ to @h_n@ can be used.
--
-- (Note: The effects in a context are partially applied types -- an effect @h e ans@
-- denotes a full effect handler (as a value) defined in an effect context @e@ and
-- with answer type @ans@. In the effect context type though, these types are abstract
-- and we use the partial type @h@ do denote the effect)
data (h :: * -> * -> *) :* e

-- | A runtime context @Context e@ corresponds always to the effect context @e@.
data Context e where
  CCons :: !(Marker ans) -> !(h e' ans) -> !(ContextT e e') -> !(Context e) -> Context (h :* e)
  CNil  :: Context ()

-- A context transformer: this could be defined as a regular function as
--  `type ContextT e e' = Context e -> Context e'`
-- but we use an explicit representation as a GADT for the identity and
-- `CCons` versions of the function as that allows the compiler to optimize
-- much better for the cases where the function is known.
data ContextT e e' where
  CTCons :: Marker ans -> h e' ans -> !(ContextT e e') -> ContextT e (h :* e)
  CTId   :: ContextT e e
  -- CTFun :: !(Context e -> Context e') -> ContextT e e'

-- apply a context transformer
applyT :: ContextT e e' -> Context e -> Context e'
applyT (CTCons m h g) ctx = CCons m h g ctx
applyT (CTId) ctx         = ctx
--applyT (CTFun f) ctx = f ctx

-- the tail of a context
ctail :: Context (h :* e) -> Context e
ctail (CCons _ _ _ ctx)   = ctx


-------------------------------------------------------
-- The Effect monad
-------------------------------------------------------

-- | The effect monad in an effect context @e@ with result @a@
newtype Eff e a = Eff (Context e -> Ctl a)

{-# INLINE lift #-}
lift :: Ctl a -> Eff e a
lift ctl = Eff (\_ -> ctl)

{-# INLINE under #-}
under :: Context e -> Eff e a -> Ctl a
under ctx (Eff eff)  = eff ctx


instance Functor (Eff e) where
  fmap  = liftM
instance Applicative (Eff e) where
  pure  = return
  (<*>) = ap
instance Monad (Eff e) where
  return x          = Eff (\ctx -> pure x)
  (Eff eff) >>= f   = Eff (\ctx -> do x <- eff ctx
                                      under ctx (f x))

-- | Use @handler hnd action@ to handle effect @h@ with
-- handler @hnd@ in @action@ (which has @h@ in its effect context now as @h :* e@).
-- For example:
--
-- @
-- data Reader a e ans = Reader { ask :: Op () a e ans }
--
-- reader :: a -> Eff (Reader a :* e) ans -> Eff e ans
-- reader x = handler (Reader{ ask = value x })
-- @
handler :: h e ans -> Eff (h :* e) ans -> Eff e ans
handler h action
  = Eff (\ctx -> prompt $ \m ->                      -- set a fresh prompt with marker `m`
                 do under (CCons m h CTId ctx) action) -- and call action with the extra evidence

-- | Run an effect monad in an empty context (as all effects need to be handled)
runEff :: Eff () a -> a
runEff (Eff eff)  = runCtl (eff CNil)


-- | Handle an effect @h@ over @action@ and tranform the final result with
-- the /return/ function @ret@. For example:
--
-- @
-- data Except a e ans = Except { throwError :: forall b. Op a b e ans }
--
-- exceptMaybe :: Eff (Except a :* e) ans -> Eff e (Maybe ans)
-- exceptMaybe = handlerRet Just (Except{ throwError = except (\_ -> return Nothing) })
-- @
handlerRet :: (ans -> a) -> h e a -> Eff (h :* e) ans -> Eff e a
handlerRet ret h action
  = handler h (do x <- action; return (ret x))


-- | Define a handler @h@ that hides the top handler @h'@ from its @action@,
-- while keeping @h'@ is still visible in the operation definitions of @h@.
-- This is used to implement locally isolated state for `handlerLocal` using
-- the regular `local` state. In particular, `handlerLocal` is implemented as:
--
-- @
-- handlerLocal :: a -> (h (Local a :* e) ans) -> Eff (h :* e) ans -> Eff e ans
-- handlerLocal init h action = local init (handlerHide h action)
-- @
handlerHide :: h (h' :* e) ans -> Eff (h :* e) ans -> Eff (h' :* e) ans
handlerHide h action
  = Eff (\(CCons m' h' g' ctx') -> prompt (\m -> under (CCons m h (CTCons m' h' g') ctx') action))


-- | Mask the top effect handler in the give action (i.e. if a operation is performed
-- on an @h@ effect inside @e@ the top handler is ignored).
mask :: Eff e ans -> Eff (h :* e) ans
mask (Eff f) = Eff (\ctx -> f (ctail ctx))


---------------------------------------------------------
-- Select a sub context
---------------------------------------------------------

{-| An effect membership constraint: @h :? e@ ensures that the effect handler
@h@ is in the effect context @e@. For example:

@
inc :: (State Int :? e) => Eff e ()
inc = do i <- perform get ()
         perform put (i+1) }
@

-}
type h :? e = In h e   -- is `h` in the effect context `e` ?

data SubContext h  = forall e. SubContext !(Context (h :* e))  -- make `e` existential

-- | The @In@ constraint is an alias for `:?`
class In h e where
  subContext :: Context e -> SubContext h  -- ^ Internal method to select a sub context

instance (InEq (HEqual h h') h h' w) => In h (h' :* w)  where
  subContext = subContextEq


type family HEqual (h :: * -> * -> *) (h' :: * -> * -> *) :: Bool where
  HEqual h h  = 'True
  HEqual h h' = 'False

-- | Internal class used by `:?`.
class (iseq ~ HEqual h h') => InEq iseq h h' e  where
  subContextEq :: Context (h' :* e) -> SubContext h

instance (h ~ h') => InEq 'True h h' e where
  subContextEq ctx = SubContext ctx

instance ('False ~ HEqual h h', In h e) => InEq 'False h h' e where
  subContextEq ctx = subContext (ctail ctx)

{-# INLINE withSubContext #-}
withSubContext :: (In h e) => (SubContext h -> Ctl a) -> Eff e a
withSubContext f
  = Eff (\ctx -> f (subContext ctx))


------------------------------------------------------------------------
-- Allow giving closed type signature (like `State Int :* Amb :* ()`)
-- and later open it up in another context
------------------------------------------------------------------------
{-
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
-}


------------------------------------
-- Operations
-------------------------------------

-- | The abstract type of operations of type @a@ to @b@, for a handler
-- defined in an effect context @e@ and answer type @ans@.
data Op a b e ans = Op { applyOp :: !(Marker ans -> Context e -> a -> Ctl b) }

{-| Given an operation selector, perform the operation. The type of the selector
function is a bit intimidating, but it just selects the right operation @Op@ from the
handler @h@ regardless of the effect context @e'@ and answer type @ans@ where the
handler is defined.

Usually the operation selector is a field in the data type for the effect handler.
For example:

@
data Reader a e ans = Reader{ ask :: Op () a e ans }

greet :: (Reader String :? e) => Eff e String
greet = do s <- perform ask ()
           return ("hello " ++ s)

test = runEff $
       handler (Reader{ ask = value "world" }) $
       greet
@

-}
{-# INLINE perform #-}
perform :: (h :? e) => (forall e' ans. h e' ans -> Op a b e' ans) -> a -> Eff e b
perform selectOp x
  = withSubContext (\(SubContext (CCons m h g ctx)) -> applyOp (selectOp h) m (applyT g ctx) x)

-- | Create an operation that always resumes with a constant value (of type @a@).
-- (see also the `perform` example).
{-# INLINE value #-}
value :: a -> Op () a e ans
value x = function (\() -> return x)

-- | Create an operation that takes an argument of type @a@ and always resumes with a result of type @b@.
-- These are called /tail-resumptive/ operations and are implemented more efficient than
-- general operations as they can execute /in-place/ (instead of yielding to the handler).
-- Most operations are tail-resumptive. (See also the `handlerLocal` example).
{-# INLINE function #-}
function :: (a -> Eff e b) -> Op a b e ans
function f = Op (\_ ctx x -> under ctx (f x))


-- | Create an fully general operation from type @a@ to @b@.
-- the function @f@ takes the argument, and a /resumption/ function of type @b -> Eff e ans@
-- that can be called to resume from the original call site. For example:
--
-- @
-- data Amb e ans = Amb { flip :: forall b. Op () Bool e ans }
--
-- xor :: (Amb :? e) => Eff e Bool
-- xor = do x <- perform flip ()
--          y <- perform flip ()
--          return ((x && not y) || (not x && y))
--
-- solutions :: Eff (Amb :* e) a -> Eff e [a]
-- solutions = handlerRet (\\x -> [x]) $
--             Amb{ flip = operation (\\() k -> do{ xs <- k True; ys <- k False; return (xs ++ ys)) }) }
-- @
operation :: (a -> (b -> Eff e ans) -> Eff e ans) -> Op a b e ans
operation f = Op (\m ctx x -> yield m $ \ctlk ->
                              let k y = Eff (\ctx' -> guard ctx ctx' ctlk y)
                              in under ctx (f x k))


-- | Create an operation that never resumes (an exception).
-- (See `handlerRet` for an example).
except :: (a -> Eff e ans) -> Op a b e ans
except f = operation (\x _ -> f x)


guard :: Context e -> Context e -> (b -> Ctl a) -> b -> Ctl a
guard ctx1 ctx2 k x = if (ctx1 == ctx2) then k x else error "Control.Ev.Eff.guard: unscoped resumption under a different handler context"

instance Eq (Context e) where
  (CCons m1 _ _ ctx1)  == (CCons m2 _ _ ctx2)   = (markerEq m1 m2) && (ctx1 == ctx2)
  CNil                 == CNil                  = True


--------------------------------------------------------------------------------
-- Efficient (and safe) Local state handler
--------------------------------------------------------------------------------
-- | The type of the built-in state effect.
-- (This state is generally more efficient than rolling your own and usually
-- used in combination with `handlerLocal` to provide local isolated state)
newtype Local a e ans = Local (IORef a)

-- | Get the value of the local state.
{-# INLINE lget #-}
lget :: Local a e ans -> Op () a e ans
lget (Local r) = Op (\m ctx x -> unsafeIO (readIORef r))

-- | Set the value of the local state.
{-# INLINE lput #-}
lput :: Local a e ans -> Op a () e ans
lput (Local r) = Op (\m ctx x -> unsafeIO (writeIORef r x))

-- | Update the value of the local state.
{-# INLINE lupdate #-}
lupdate :: Local a e ans -> Op (a -> a) () e ans
lupdate (Local r) = Op (\m ctx f -> unsafeIO (do{ x <- readIORef r; writeIORef r (f x) }))

-- | Get the value of the local state if it is the top handler.
localGet :: Eff (Local a :* e) a
localGet = perform lget ()

-- | Set the value of the local state if it is the top handler.
localPut :: a -> Eff (Local a :* e) ()
localPut x = perform lput x

-- | Update the value of the local state if it is the top handler.
localUpdate :: (a -> a) -> Eff (Local a :* e) ()
localUpdate f = perform lupdate f

-- | Create a local state handler.
{-# INLINE local #-}
local :: a -> Eff (Local a :* e) ans -> Eff e ans
local init action
  = Eff (\ctx -> promptIORef init $ \m r ->  -- set a fresh prompt with marker `m`
                 do under (CCons m (Local r) CTId ctx) action) -- and call action with the extra evidence

-- | Create a new handler for @h@ which can access the /locally isolated state/ @Local a@.
-- This is fully local to the handler @h@ only and not visible in the @action@ as
-- apparent from its effect context (which does /not/ contain @Local a@). The
-- @ret@ argument can be used to transform the final result type.
{-# INLINE handlerLocalRet #-}
handlerLocalRet :: a -> (ans -> a -> b) -> (h (Local a :* e) ans) -> Eff (h :* e) ans -> Eff e b
handlerLocalRet init ret h action
  = local init $ do x <- handlerHide h action
                    y <- localGet
                    return (ret x y)

-- | Create a new handler for @h@ which can access the /locally isolated state/ @Local a@.
-- This is fully local to the handler @h@ only and not visible in the @action@ as
-- apparent from its effect context (which does /not/ contain @Local a@).
--
-- @
-- data State a e ans = State { get :: Op () a e ans, put :: Op a () e ans  }
--
-- state :: a -> Eff (State a :* e) ans -> Eff e ans
-- state init = handlerLocal init (State{ get = function (\\_ -> perform lget ()),
--                                        put = function (\\x -> perform lput x) })
--
-- test = runEff $
--        state (41::Int) $
--        inc                -- see `:?`
-- @
{-# INLINE handlerLocal #-}
handlerLocal :: a -> (h (Local a :* e) ans) -> Eff (h :* e) ans -> Eff e ans
handlerLocal init h action
  = local init (handlerHide h action)
