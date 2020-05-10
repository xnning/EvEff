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

module Control.Ev.Eff(
            -- Effect monad
              Eff
            , runEff          -- :: Eff () a -> a
            , (:*)            -- h :* e
            , In, (:?)        -- h :? e

            -- operations
            , Op
            , value           -- :: a -> Op () a e ans
            , function        -- :: (a -> Eff e b) -> Op a b e ans
            , except          -- :: (a -> Eff e ans) -> Op a b e ans
            , operation       -- :: (a -> (b -> Eff e ans)) -> Op a b e ans
            , perform         -- :: (h :? e) => (forall e' ans. h e' ans -> Op a b e' ans) -> a -> Eff e b

            , Linear(..)
            , lfunction
            , lvalue
            , lperform

            -- handling
            , handler         -- :: h e ans -> Eff (h :* e) ans -> Eff e ans
            , handlerRet      -- :: (ans -> b) -> h e b -> Eff (h :* e) ans -> Eff e b
            , handlerHide     -- :: h (h' :* e) ans -> Eff (h :* e) ans -> Eff (h' :* e) ans
            , mask            -- :: Eff e ans -> Eff (h :* e) ans

            -- local variables
            , Local, LocalState -- Local a e ans == Linear (LocalState a) e ans
            , local           -- :: a -> Eff (Local a :* e) ans -> Eff e ans
            , lget            -- :: (Local a :? e) => Eff e a
            , lput            -- :: (Local a :? e) => a -> Eff e ()
            , lupdate         -- :: (Local a :? e) => (a -> a) -> Eff e ()

            , localGet        -- :: Eff (Local a :* e) a
            , localPut        -- :: a -> Eff (Local a :* e) ()
            , localUpdate     -- :: (a -> a) -> Eff (Local a :* e) a

            , handlerLocal    -- :: a -> h (Local a :* e) ans -> Eff (h :* e) ans -> Eff e ans
            , handlerLocalRet -- :: a -> (ans -> a -> b) -> h (Local a :* e) b -> Eff (h :* e) ans -> Eff e b

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
data (h :: * -> * -> *) :* e

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


handler :: h e ans -> Eff (h :* e) ans -> Eff e ans
handler h action
  = Eff (\ctx -> prompt $ \m ->                      -- set a fresh prompt with marker `m`
                 do under (CCons m h CTId ctx) action) -- and call action with the extra evidence

runEff :: Eff () a -> a
runEff (Eff eff)  = runCtl (eff CNil)

handlerRet :: (ans -> a) -> h e a -> Eff (h :* e) ans -> Eff e a
handlerRet f h action
  = handler h (do x <- action; return (f x))



-- A handler `h` that hides one handler `h'` in its action, but `h'` is visible in the operation definitions of `h`
handlerHide :: h (h' :* e) ans -> Eff (h :* e) ans -> Eff (h' :* e) ans
handlerHide h action
  = Eff (\(CCons m' h' g' ctx') -> prompt $ \m -> --let g ctx = CCons m' h' g' ctx
                                                  under (CCons m h (CTCons m' h' g') ctx') action)



-- ignore the top effect handler
mask :: Eff e ans -> Eff (h :* e) ans
mask (Eff f) = Eff (\ctx -> f (ctail ctx))


---------------------------------------------------------
-- Select a sub context
---------------------------------------------------------
type h :? e = In h e   -- is `h` in the effect context `e` ?

data SubContext h  = forall e. SubContext !(Context (h :* e))  -- make `e` existential

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
-- Operations of type `a -> b` in a handler context `ans`
data Op a b e ans = Op { useOp :: !(Marker ans -> Context e -> a -> Ctl b) }

-- Given evidence and an operation selector, perform the operation
-- perform :: In h e => (forall e' ans. Handler h e' ans -> Clause a b e' ans) -> a -> Eff e b
{-# INLINE perform #-}
perform :: In h e => (forall e' ans. h e' ans -> Op a b e' ans) -> a -> Eff e b
perform selectOp x
  = withSubContext (\(SubContext (CCons m h g ctx)) -> useOp (selectOp h) m (applyT g ctx) x)

-- tail-resumptive value operation (reader)
{-# INLINE value #-}
value :: a -> Op () a e ans
value x = function (\() -> return x)

-- tail-resumptive operation (almost all operations)
{-# INLINE function #-}
function :: (a -> Eff e b) -> Op a b e ans
function f = Op (\_ ctx x -> under ctx (f x))


-- general operation with a resumption (exceptions, async/await, etc)
operation :: (a -> (b -> Eff e ans) -> Eff e ans) -> Op a b e ans
operation f = Op (\m ctx x -> yield m $ \ctlk ->
                              let k y = Eff (\ctx' -> guard ctx ctx' ctlk y)
                              in under ctx (f x k))


-- operation that never resumes
except :: (a -> Eff e ans) -> Op a b e ans
except f = operation (\x _ -> f x)


guard :: Context e -> Context e -> (b -> Ctl a) -> b -> Ctl a
guard ctx1 ctx2 k x = if (ctx1 == ctx2) then k x else error "Control.Ev.Eff.guard: unscoped resumption under a different handler context"

instance Eq (Context e) where
  (CCons m1 _ _ ctx1)  == (CCons m2 _ _ ctx2)   = (markerEq m1 m2) && (ctx1 == ctx2)
  CNil                 == CNil                  = True


--------------------------------------------------------------------------------
-- Linear effect operations never yield
--------------------------------------------------------------------------------
newtype Linear h e ans  = Linear{ unlinear :: (h e ans) }

{-# INLINE lperform #-}
lperform :: In (Linear h) e => (forall e' ans. h e' ans -> Op a b e' ans) -> a -> Eff e b
lperform selectOp x
  = withSubContext $ \(SubContext (CCons m h g ctx)) ->
    case useOp (selectOp (unlinear h)) m (applyT g ctx) x of
      ctl@(Pure _) -> ctl
      _            -> error "Control.Ev.Eff.lperform: linear operation yielded!"

-- linear tail-resumptive operation (almost all operations)
{-# INLINE lfunction #-}
lfunction :: (a -> Eff e b) -> Op a b e ans
lfunction f = Op (\_ ctx x -> case (under ctx (f x)) of
                                ctl@(Pure _) -> ctl
                                _            -> error "Control.Ev.Eff.lfunction: operation declared as linear but it yielded!")

-- linear value
{-# INLINE lvalue #-}
lvalue :: a -> Op () a e ans
lvalue x = lfunction (\() -> return x)

--------------------------------------------------------------------------------
-- Efficient (and safe) Local state handler
--------------------------------------------------------------------------------

newtype LocalState a e ans = Local (IORef a)

type Local a = Linear (LocalState a)

{-# INLINE lget #-}
lget :: LocalState a e ans -> Op () a e ans
lget (Local r) = Op (\m ctx x -> unsafeIO (readIORef r))

{-# INLINE lput #-}
lput :: LocalState a e ans -> Op a () e ans
lput (Local r) = Op (\m ctx x -> unsafeIO (writeIORef r x))

{-# INLINE lupdate #-}
lupdate :: LocalState a e ans -> Op (a -> a) () e ans
lupdate (Local r) = Op (\m ctx f -> unsafeIO (do{ x <- readIORef r; writeIORef r (f x) }))

localGet :: Eff (Local a :* e) a
localGet = lperform lget ()

localPut :: a -> Eff (Local a :* e) ()
localPut x = lperform lput x

localUpdate :: (a -> a) -> Eff (Local a :* e) ()
localUpdate f = lperform lupdate f


{-# INLINE local #-}
local :: a -> Eff (Local a :* e) ans -> Eff e ans
local init action
  = Eff (\ctx -> promptIORef init $ \m r ->  -- set a fresh prompt with marker `m`
                 do under (CCons m (Linear (Local r)) CTId ctx) action) -- and call action with the extra evidence

-- Expose a local state handler to just one handler's operations
{-# INLINE handlerLocalRet #-}
handlerLocalRet :: a -> (ans -> a -> b) -> (h (Local a :* e) ans) -> Eff (h :* e) ans -> Eff e b
handlerLocalRet init ret h action
  = local init $ do x <- handlerHide h action
                    y <- localGet
                    return (ret x y)

{-# INLINE handlerLocal #-}
handlerLocal :: a -> (h (Local a :* e) ans) -> Eff (h :* e) ans -> Eff e ans
handlerLocal init h action
  = local init (handlerHide h action)
