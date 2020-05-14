{-# LANGUAGE GADTs,                       -- match on Refl for type equality
             ExistentialQuantification    -- forall b ans. Yield ...
#-}
{-|
Description : Internal module for type-safe multi-prompt control
Copyright   : (c) 2020, Microsoft Research; Daan Leijen; Ningning Xie
License     : MIT
Maintainer  : xnning@hku.hk; daan@microsoft.com
Stability   : Experimental

Primitive module that implements type safe multi-prompt control.
Used by the "Control.Ev.Eff" module to implement effect handlers.
-}
module Control.Ev.Ctl(
          -- * Markers
            Marker       -- prompt marker
          , markerEq     -- :: Marker a -> Marker b -> Bool

          -- * Control monad
          , Ctl(Pure)    -- multi-prompt control monad
          , runCtl       -- run the control monad       :: Ctl a -> a
          , prompt       -- install a multi-prompt      :: (Marker a -> Ctl a) -> Ctl a
          , yield        -- yield to a specific prompt  :: Marker ans -> ((b -> Ctl ans) -> Ctl ans) -> Ctl b

          -- * Unsafe primitives for "Control.Ev.Eff"
          , unsafeIO            -- lift IO into Ctl        :: IO a -> Ctl a
          , unsafePromptIORef   -- IORef that gets restored per resumption
          ) where

import Prelude hiding (read,flip)
import Control.Monad( ap, liftM )
import Data.Type.Equality( (:~:)( Refl ) )
import Control.Monad.Primitive

-------------------------------------------------------
-- Assume some way to generate a fresh prompt marker
-- associated with specific answer type.
-------------------------------------------------------
import Unsafe.Coerce    ( unsafeCoerce )
import System.IO.Unsafe ( unsafePerformIO )
import Data.IORef

-- | An abstract prompt marker
data Marker a = Marker !Integer

instance Show (Marker a) where
  show (Marker i) = show i

instance Eq (Marker a) where
  m1 == m2  = markerEq m1 m2

-- | Compare two markers of different types for equality
markerEq :: Marker a -> Marker b -> Bool
markerEq (Marker i) (Marker j)  = (i == j)

-- if markers match, their types are the same
mmatch :: Marker a -> Marker b -> Maybe ((:~:) a b)
mmatch (Marker i) (Marker j) | i == j  = Just (unsafeCoerce Refl)
mmatch _ _ = Nothing

-- global unique counter
unique :: IORef Integer
unique = unsafePerformIO (newIORef 0)

-- evaluate a action with a fresh marker
freshMarker :: (Marker a -> Ctl a) -> Ctl a
freshMarker f
  = let m = unsafePerformIO $
            do i <- readIORef unique;
               writeIORef unique (i+1);
               return i
    in seq m (f (Marker m))


{-|  The Multi Prompt control monad,
with existentials `ans` and `b`: where `ans` is the answer type, i.e. the type of the handler/prompt context,
and `b` the result type of the operation.
-}
data Ctl a = Pure { result :: !a }  -- ^ Pure results (only exported for use in the "Control.Ev.Eff" module)
           | forall ans b.
             Yield{ marker :: !(Marker ans),                 -- ^ prompt marker to yield to (in type context `::ans`)
                    op     :: !((b -> Ctl ans) -> Ctl ans),  -- ^ the final action, just needs the resumption (:: b -> Ctl ans) to be evaluated.
                    cont   :: !(b -> Ctl a)                  -- ^ the (partially) build up resumption; `(b -> Ctl a) :~: (b -> Ctl ans)` by the time we reach the prompt
                  }

-- | @yield m op@ yields to a specific marker and calls @op@ in that context
-- with a /resumption/ @k :: b -> Ctl ans@ that resumes at the original call-site
-- with a result of type @b@. If the marker is no longer in the evaluation context,
-- (i.e. it escaped outside its prompt) the `yield` fails with an @"unhandled operation"@ error.
{-# INLINE yield #-}
yield :: Marker ans -> ((b -> Ctl ans) -> Ctl ans) -> Ctl b
yield m op  = Yield m op Pure

{-# INLINE kcompose #-}
kcompose :: (b -> Ctl c) -> (a -> Ctl b) -> a -> Ctl c      -- Kleisli composition
kcompose g f x = case (f x) of
                   Pure x -> g x
                   Yield m op cont -> Yield m op (g `kcompose` cont)

{-# INLINE bind #-}
bind :: Ctl a -> (a -> Ctl b) -> Ctl b
bind (Pure x) f           = f x
bind (Yield m op cont) f  = Yield m op (f `kcompose` cont)  -- keep yielding with an extended continuation

instance Functor Ctl where
  fmap  = liftM
instance Applicative Ctl where
  pure  = return
  (<*>) = ap
instance Monad Ctl where
  return x  = Pure x
  e >>= f   = bind e f


-- install a prompt with a unique marker (and handle yields to it)
{-# INLINE mprompt #-}
mprompt :: Marker a -> Ctl a -> Ctl a
mprompt m (Pure x) = Pure x
mprompt m (Yield n op cont)
  = let cont' x = mprompt m (cont x) in  -- extend the continuation with our own prompt
    case mmatch m n of
      Nothing   -> Yield n op cont'   -- keep yielding (but with the extended continuation)
      Just Refl -> op cont'           -- found our prompt, invoke `op`.
                   -- Note: `Refl` proves `a ~ ans` (the existential `ans` in Yield)

-- | Install a /prompt/ with a specific prompt `Marker` to which one can `yield`.
-- This connects creation of a marker with instantiating the prompt. The marker passed
-- to the @action@ argument should not escape the @action@ (but this is not statically checked,
-- only at runtime when `yield`ing to it).
{-# INLINE prompt #-}
prompt :: (Marker a -> Ctl a) -> Ctl a
prompt action
  = freshMarker $ \m ->   -- create a fresh marker
    mprompt m (action m)  -- and install a prompt associated with this marker

-- | Run a control monad. This may fail with an @"unhandled operation"@ error if 
-- there is a `yield` to a marker that escaped its prompt scope.
runCtl :: Ctl a -> a
runCtl (Pure x)      = x
runCtl (Yield _ _ _) = error "Unhandled operation"  -- only if marker escapes the scope of the prompt


-------------------------------------------------------
-- IORef's
-------------------------------------------------------

-- | Unsafe `IO` in the `Ctl` monad.
{-# INLINE unsafeIO #-}
unsafeIO :: IO a -> Ctl a
unsafeIO io = let x = unsafeInlinePrim io in seq x (Pure x)

-- A special prompt that saves and restores state per resumption
mpromptIORef :: IORef a -> Ctl b -> Ctl b
mpromptIORef r action
  = case action of
      Pure x -> pure x
      Yield m op cont
        -> do val <- unsafeIO (readIORef r)                 -- save current value on yielding
              let cont' x = do unsafeIO (writeIORef r val)  -- restore saved value on resume
                               mpromptIORef r (cont x)
              Yield m op cont'

-- | Create an `IORef` connected to a prompt. The value of
-- the `IORef` is saved and restored through resumptions.
unsafePromptIORef :: a -> (Marker b -> IORef a -> Ctl b) -> Ctl b
unsafePromptIORef init action
  = freshMarker $ \m ->
    do r <- unsafeIO (newIORef init)
       mpromptIORef r (action m r)


{-
{-# INLINE mlocalGet #-}
mlocalGet :: Local a -> b -> Ctl a
mlocalGet (Local r) x = unsafeIO (seq x $ readIORef r)

{-# INLINE mlocalSet #-}
mlocalSet :: Local a -> a -> Ctl ()
mlocalSet (Local r) x = unsafeIO (writeIORef r x)


localOutOfScope :: Local a -> Ctl a
localOutOfScope local
  =  do x <- mlocalGet local ()
        -- mlocalSet local (error "local state is accessed outside its scope")
        return x

mlocal :: a -> (Local a -> Ctl b) -> Ctl b
mlocal init action
  = do ref <- unsafeIO (newIORef init)
       let local = Local ref
       plocal local (action local)

plocal :: Local a -> Ctl b -> Ctl b
plocal local action
  = case action of
      Pure x -> do localOutOfScope local
                   pure x
      Yield m op cont
        -> do val <- localOutOfScope local            -- save current value
              let cont' x = do mlocalSet local val    -- restore saved value on resume
                               plocal local (cont x)
              Yield m op cont'
-}
