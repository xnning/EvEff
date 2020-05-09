-----------------------------------------------------
-- Copyright 2020, Daan Leijen.
-----------------------------------------------------
{-# LANGUAGE GADTs,                       -- match on Refl for type equality
             ExistentialQuantification    -- forall b ans. Control ...
#-}
module Control.Ev.Ctl(
            Marker       -- prompt marker
          , markerEq     -- :: Marker a -> Marker b -> Bool

          , Ctl          -- control monad
          , runCtl       -- run the control monad   :: Ctl a -> a
          , prompt       -- install prompt          :: Marker a -> Ctl a -> Ctl a
          , yield        -- yield to a prompt       :: Marker ans -> ((b -> Ctl ans) -> Ctl ans) -> Ctl b

          , unsafeIO     -- lift IO into Ctl        :: IO a -> Ctl a
          ) where

import Prelude hiding (read,flip)
import Control.Monad( ap, liftM )
import Data.Type.Equality( (:~:)( Refl ) )
import Control.Monad.Primitive
-------------------------------------------------------
-- Assume some way to generate a fresh prompt marker
-- associated with specific answer type.
-------------------------------------------------------
import Unsafe.Coerce     (unsafeCoerce)
import System.IO.Unsafe ( unsafePerformIO )
import Data.IORef

-- an abstract marker
data Marker a = Marker !Integer

instance Show (Marker a) where
  show (Marker i) = show i

instance Eq (Marker a) where
  m1 == m2  = markerEq m1 m2

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


-------------------------------------------------------
-- The Multi Prompt control monad
-- ans: the answer type, i.e. the type of the handler/prompt context
-- b  : the result type of the operation
-------------------------------------------------------
data Ctl a = Pure { result :: !a }
           | forall ans b.
             Control{ marker :: !(Marker ans),                 -- prompt marker to yield to (in type context `::ans`)
                      op     :: !((b -> Ctl ans) -> Ctl ans),  -- the final action, just needs the resumption (:: b -> Ctl ans) to be evaluated.
                      cont   :: !(b -> Ctl a) }                -- the (partially) build up resumption; (b -> Ctl a) :~: (b -> Ctl ans)` by the time we reach the prompt

-- start yielding (with an initially empty continuation)
{-# INLINE yield #-}
yield :: Marker ans -> ((b -> Ctl ans) -> Ctl ans) -> Ctl b
yield m op  = Control m op Pure

{-# INLINE kcompose #-}
kcompose :: (b -> Ctl c) -> (a -> Ctl b) -> a -> Ctl c      -- Kleisli composition
kcompose g f x = case (f x) of
                   Pure x -> g x
                   Control m op cont -> Control m op (g `kcompose` cont)

{-# INLINE bind #-}
bind :: Ctl a -> (a -> Ctl b) -> Ctl b
bind (Pure x) f             = f x
bind (Control m op cont) f  = Control m op (f `kcompose` cont)  -- keep yielding with an extended continuation

instance Functor Ctl where
  fmap  = liftM
instance Applicative Ctl where
  pure  = return
  (<*>) = ap
instance Monad Ctl where
  return x  = Pure x
  e >>= f   = bind e f


-- use a prompt with a unique marker (and handle yields to it)
{-# INLINE mprompt #-}
mprompt :: Marker a -> Ctl a -> Ctl a
mprompt m (Pure x) = Pure x
mprompt m (Control n op cont)
  = let cont' x = mprompt m (cont x) in  -- extend the continuation with our own prompt
    case mmatch m n of
      Nothing   -> Control n op cont'   -- keep yielding (but with the extended continuation)
      Just Refl -> op cont'             -- found our prompt, invoke `op`.
                   -- Note: `Refl` proves `a ~ ans` (the existential `ans` in Control)

-- connect creation of a marker with instantiating the prompt
{-# INLINE prompt #-}
prompt :: (Marker a -> Ctl a) -> Ctl a
prompt action
  = freshMarker $ \m ->  -- create a fresh marker
    mprompt m (action m)  -- and install a prompt associated with this marker

-- Run a control monad
runCtl :: Ctl a -> a
runCtl (Pure x) = x
runCtl (Control _ _ _) = error "Unhandled operation"  -- only if marker escapes the scope of the prompt


-------------------------------------------------------
-- Optional: local state
-------------------------------------------------------
newtype Local a = Local (IORef a)

{-# INLINE unsafeIO #-}
unsafeIO :: IO a -> Ctl a
unsafeIO io = let x = unsafeInlinePrim io in seq x (Pure x)


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
      Control m op cont
        -> do val <- localOutOfScope local            -- save current value
              let cont' x = do mlocalSet local val    -- restore saved value on resume
                               plocal local (cont x)
              Control m op cont'
