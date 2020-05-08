{-# LANGUAGE TypeOperators, FlexibleContexts, Rank2Types, MagicHash #-}
module Library where

import Prelude
import Ctl
import EffEvScoped
import GHC.Prim
import GHC.Exts

------------
-- State
------------

data State a e ans = State { get_ :: !(Op () a e ans)
                           , put_ :: !(Op a () e ans)  }

{-# INLINE get #-}
get :: (State a :? e)  => Eff e a
get = perform get_ ()

{-# INLINE put #-}
put :: (State a :? e)  => a -> Eff e ()
put i = (perform put_ i)

-- A monadic state handler
-- Note: can be done more efficient with parameterized control
mstate :: State a e (a -> Eff e ans)
mstate = State { get_ = Normal (\() k -> return $ \s -> (k s  >>= \r -> r s ))
               , put_ = Normal (\s  k -> return $ \_ -> (k () >>= \r -> r s))
               }

-- NINGNING: this version seems faster for eff local.
--           But it's not a fair comparison.
-- runNext :: (State Int :? e) => Int -> Eff e Int
-- runNext i = if (i == 0) then return i
--              else put (i-1) >>= runCount

-- {-# NOINLINE runCount #-}
-- runCount :: (State Int :? e) => () -> Eff e Int
-- runCount () = get >>= runNext


runCount :: (State Int :? e) => () -> Eff e Int
runCount () = do i <- get
                 if (i == 0) then return i
                   else put (i-1) >>= runCount


count :: Int -> (Int, Int)
count n = erun $
            do let ret x = return (\s -> return (x,s))
               f <- handle mstate $
                      do x <- runCount ()
                         ret x
               f n

------------------------------------
-- Local state
-------------------------------------
lstate :: a -> Eff (State a :* e) ans -> Eff e ans
lstate init action
  = local init $ \l ->
    let h = State { get_ = opTail (\x -> localGet l x),
                    put_ = opTail (\x -> localSet l x) }
    in handle h action

hlocal :: p -> (Local p -> h e ans) -> Eff (h :* e) ans -> Eff e ans
hlocal init hcreate action
  = local init $ \l -> handle (hcreate l) action


lstate' init
  = hlocal init $ \l ->
    State { get_ = opTail (\x -> localGet l x),
            put_ = opTail (\x -> localSet l x) }

{-
safeLocalGet :: Local s a -> Eff e a
loc :: exists s. Local s Integer
(\x -> safeLocalGet loc + x) :: Int -> Eff e Int
-}
{-

newtype SLocal s a = SLocal (Local a)

slocalGet :: SLocal s a -> a -> Eff (Localized s :* e) a
slocalGet (SLocal l) x = localGet l x
slocalSet (SLocal l) x = localSet l x

data Localized s e ans = Localized

slocal :: a -> (forall s. SLocal s a -> Eff e b) -> Eff e b
slocal init action = Eff (\w -> mlocal init (\l ->
                                mprompt $ \m ->
                                under w (action (SLocal l))))

unlocalize :: (h (Localized s :* e) ans) -> h e ans

hslocal :: p -> (forall s. SLocal s p -> h (Localized s :* e) ans) -> Eff (h :* e) ans -> Eff e ans
hslocal init hcreate action
  = slocal init $ \l -> handle (unlocalize (hcreate l)) action




data LEvil e ans = LEvil { leak :: !(Op () (Int -> Eff () Int) e ans) }

levil init
  = hslocal init $ \l ->
    LEvil { leak = opTail (\x -> return (\x -> slocalGet l x))}

weird :: Int -> Int
weird n = erun $
          do f <- levil 42 $ perform leak ()
             f 1

-}
lCount :: Int -> Int
lCount n = erun $ lstate' n $
           do x <- runCount ()
              return x

main :: IO ()
main = do let x = lCount (10^6)
          print x


------------------------------------
-- Parameterized handler
-------------------------------------
newtype Parameter s a = Parameter (Local a)

pNormal :: Parameter s p -> (a -> p -> ((b,p) -> Eff e ans) -> Eff e ans) -> Op a b e ans
pNormal (Parameter p) op
  = Normal (\x k -> do vx <- localGet p x
                       let kp (y,vy) = do{ localSet p vy; k y }
                       op x vx kp)

pTail :: Parameter s p -> (a -> p -> Eff e (b,p)) -> Op a b e ans
pTail (Parameter p) op
 = opTail (\x -> do vx <- localGet p x
                    (y,vy) <- op x vx
                    localSet p vy
                    return y)

phandle :: (forall s. Parameter s p -> h e ans) -> p -> Eff (h :* e) ans -> Eff e ans
phandle hcreate init action
  = local init $ \local ->
    let p = Parameter local
    in handle (hcreate p) action

------
pstate :: Parameter s a -> State a e ans
pstate p = State { get_ = pTail p (\() v -> return (v,v)),
                   put_ = pTail p (\x v  -> return ((),x)) }


pCount :: Int -> Int
pCount n = erun $
           phandle pstate (n::Int) $
             do x <- runCount ()
                return x

------------
-- Write
------------

data Writer a e ans = Writer { tell_ :: !(Op a () e ans) }

{-# INLINE tell #-}
tell :: (Writer a :? e) => a -> Eff e ()
tell = perform tell_

writer :: (Monoid a) => a -> Eff (Writer a :* e) ans -> Eff e (a, ans)
{-# INLINE writer #-}
writer init action
  = local init $ \l ->
      let h = Writer { tell_ = opTail (\x -> do y <- localGet l x
                                                localSet l (mappend y x)) }
      in do y <- handle h action
            x <- localGet l init
            return (x, y)

------------
-- Exn
------------

data Exn e ans = Exn { throwError_ :: forall a. Op String a e ans }

throwError :: In Exn e  => String -> Eff e a
throwError = perform throwError_

exn :: Exn e (Either String a)
exn = Exn (Normal (\msg resume -> return $ Left msg))


---------------------------------------
-- non-tail
---------------------------------------

lstateNonTail :: a -> Eff (State a :* e) ans -> Eff e ans
lstateNonTail init action
  = local init $ \l ->
    let h = State { get_ = Normal (\x k -> do y <- localGet l x; k y),
                    put_ = Normal (\x k -> do localSet l x; k ()) }
    in handle h action

writerNonTail :: (Monoid a) => a -> Eff (Writer a :* e) ans -> Eff e (a, ans)
{-# INLINE writerNonTail #-}
writerNonTail init action
  = local init $ \l ->
      let h = Writer { tell_ = Normal (\x k -> do y <- localGet l x
                                                  localSet l (mappend y x)
                                                  k ()) }
      in do y <- handle h action
            x <- localGet l init
            return (x, y)
