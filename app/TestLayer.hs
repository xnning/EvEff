{-# LANGUAGE
    FlexibleContexts
  , AllowAmbiguousTypes -- Extensible Effects
  , TypeOperators
#-}
module TestLayer where

import Data.List
import Criterion.Main
import Criterion.Types

-- runST
import Control.Monad.ST
import Data.STRef

-- MTL
import Control.Monad (foldM)
import qualified Control.Monad.State as Ms
import qualified Control.Monad.Reader as Mr

-- Extensible Effects
import qualified Control.Eff as EE
import qualified Control.Eff.State.Lazy as EEs
import qualified Control.Eff.Reader.Lazy as EEr

-- Fused Effects
import qualified Control.Algebra as F
import qualified Control.Carrier.State.Lazy as Fs
import qualified Control.Carrier.Reader as Fr

-- Eff
import Control.Ev.Eff
import Control.Ev.Util

-------------------------------------------------------
-- Pure
-------------------------------------------------------

layerPure :: Integer -> Integer
layerPure n = fst (foldl' f (1,0) [n, n-1 .. 0])
  where f (acc,st) x | x `mod` 5 == 0 = let st' = st+1 in seq st' (max acc x, st')
        f (acc,st) x = (max acc x, st)

-------------------------------------------------------
-- Pure
-------------------------------------------------------

countST :: STRef s Integer -> Integer -> ST s Integer
countST r n = foldM f 1 [n, n-1 .. 0]
  where f acc x | x `mod` 5 == 0 = do n <- readSTRef r
                                      writeSTRef r (n+1)
                                      return (max acc x)
        f acc x = return (max acc x)

layerST :: Integer -> Integer
layerST n
  = runST (do r <- newSTRef (0::Integer)
              countST r n)
              
-------------------------------------------------------
-- MONADIC
-------------------------------------------------------

monadic :: (Ms.MonadState Integer m) => Integer -> m Integer
monadic n = foldM f 1 [n, n-1 .. 0]
  where f acc x | x `mod` 5 == 0 = do n <- Ms.get
                                      Ms.put (n+1)
                                      return (max acc x)
        f acc x = return (max acc x)


-- print? why?
layerMonadic n =
  Ms.runState (monadic n) 0

-- LAYER OVER

layerOverMonadic1 n =
  flip Mr.runReader (0::Int) $
   Ms.runStateT (monadic n) 0

layerOverMonadic2 n =
  flip Mr.runReader (0::Int) $
  flip Mr.runReaderT (0::Integer) $
    Ms.runStateT (monadic n) 0

layerOverMonadic3 n =
  flip Mr.runReader (0::Int) $
  flip Mr.runReaderT (0::Integer) $
  flip Mr.runReaderT True $
    Ms.runStateT (monadic n) 0

layerOverMonadic4 n =
  flip Mr.runReader (0::Int) $
  flip Mr.runReaderT (0::Integer) $
  flip Mr.runReaderT True $
  flip Mr.runReaderT "0" $
    Ms.runStateT (monadic n) 0

layerOverMonadic5 n =
  flip Mr.runReader (0::Int) $
  flip Mr.runReaderT (0::Integer) $
  flip Mr.runReaderT True $
  flip Mr.runReaderT "0" $
  flip Mr.runReaderT 'c' $
  Ms.runStateT (monadic n) 0

layerOverMonadic6 n =
  flip Mr.runReader (0::Int) $
  flip Mr.runReaderT (0::Integer) $
  flip Mr.runReaderT True $
  flip Mr.runReaderT "0" $
  flip Mr.runReaderT 'c' $
  flip Mr.runReaderT (True,True) $
  Ms.runStateT (monadic n) 0

-- LAYER UNDER

layerUnderMonadic1 n =
    flip Ms.runState 0 $
     flip Mr.runReaderT (0::Int) $
      monadic n

layerUnderMonadic2 n =
    flip Ms.runState 0 $
     flip Mr.runReaderT (0::Int) $
     flip Mr.runReaderT (0::Integer) $
      monadic n

layerUnderMonadic3 n =
    flip Ms.runState 0 $
     flip Mr.runReaderT (0::Int) $
     flip Mr.runReaderT (0::Integer) $
     flip Mr.runReaderT True $
      monadic n

layerUnderMonadic4 n =
    flip Ms.runState 0 $
     flip Mr.runReaderT (0::Int) $
     flip Mr.runReaderT (0::Integer) $
     flip Mr.runReaderT True $
     flip Mr.runReaderT "0" $
      monadic n

layerUnderMonadic5 n =
    flip Ms.runState 0 $
     flip Mr.runReaderT (0::Int) $
     flip Mr.runReaderT (0::Integer) $
     flip Mr.runReaderT True $
     flip Mr.runReaderT "0" $
     flip Mr.runReaderT 'c' $
      monadic n

layerUnderMonadic6 n =
    flip Ms.runState 0 $
     flip Mr.runReaderT (0::Int) $
     flip Mr.runReaderT (0::Integer) $
     flip Mr.runReaderT True $
     flip Mr.runReaderT "0" $
     flip Mr.runReaderT 'c' $
     flip Mr.runReaderT (True,True) $
      monadic n

-------------------------------------------------------
-- EXTENSIBLE EFFECT
-------------------------------------------------------

ee :: (EE.Member (EEs.State Integer) r) => Integer -> EE.Eff r Integer
ee n = foldM f 1 [n, n-1 .. 0]
  where f acc x | x `mod` 5 == 0 = do n <- EEs.get
                                      EEs.put (n+1)
                                      return (max acc x)
        f acc x = return (max acc x)

layerEE n = EE.run $
  EEs.runState 0 (ee n) -- saved one annotation

-- LAYER OVER

layerOverEE1 n = EE.run $
  EEr.runReader (0::Int) $
    EEs.runState (0::Integer) (ee n)

layerOverEE2 n = EE.run $
  EEr.runReader (0::Int) $
  EEr.runReader (0::Integer) $
    EEs.runState (0::Integer) (ee n)

layerOverEE3 n = EE.run $
  EEr.runReader (0::Int) $
  EEr.runReader (0::Integer) $
  EEr.runReader True $
    EEs.runState (0::Integer) (ee n)

layerOverEE4 n = EE.run $
  EEr.runReader (0::Int) $
  EEr.runReader (0::Integer) $
  EEr.runReader True $
  EEr.runReader "0" $
    EEs.runState (0::Integer) (ee n)

layerOverEE5 n = EE.run $
  EEr.runReader (0::Int) $
  EEr.runReader (0::Integer) $
  EEr.runReader True $
  EEr.runReader "0" $
  EEr.runReader 'c' $
    EEs.runState (0::Integer) (ee n)

layerOverEE6 n = EE.run $
  EEr.runReader (0::Int) $
  EEr.runReader (0::Integer) $
  EEr.runReader True $
  EEr.runReader "0" $
  EEr.runReader 'c' $
  EEr.runReader (True,True) $
    EEs.runState (0::Integer) (ee n)
-- LAYER UNDER

layerUnderEE1 n = EE.run $
  EEs.runState (0::Integer) $
    EEr.runReader (0::Int) $
    ee n

layerUnderEE2 n = EE.run $
  EEs.runState (0::Integer) $
    EEr.runReader (0::Int) $
    EEr.runReader (0::Integer) $
    ee n

layerUnderEE3 n = EE.run $
  EEs.runState (0::Integer) $
    EEr.runReader (0::Int) $
    EEr.runReader (0::Integer) $
    EEr.runReader True $
    ee n

layerUnderEE4 n = EE.run $
  EEs.runState (0::Integer) $
    EEr.runReader (0::Int) $
    EEr.runReader (0::Integer) $
    EEr.runReader True $
    EEr.runReader "0" $
    ee n

layerUnderEE5 n = EE.run $
  EEs.runState (0::Integer) $
    EEr.runReader (0::Int) $
    EEr.runReader (0::Integer) $
    EEr.runReader True $
    EEr.runReader "0" $
    EEr.runReader 'c' $
    ee n

layerUnderEE6 n = EE.run $
  EEs.runState (0::Integer) $
    EEr.runReader (0::Int) $
    EEr.runReader (0::Integer) $
    EEr.runReader True $
    EEr.runReader "0" $
    EEr.runReader 'c' $
    EEr.runReader (True,True) $
    ee n

-------------------------------------------------------
-- Fused Effects
-------------------------------------------------------

fe :: (F.Has (Fs.State Integer) sig m) => Integer -> m Integer
fe n = foldM f 1 [n, n-1 .. 0]
  where f acc x | x `mod` 5 == 0 = do n <- Fs.get
                                      Fs.put (n+1)
                                      return (max acc x)
        f acc x = return (max acc x)

layerF n = F.run $
    Fs.runState (0::Integer) (fe n)

layerOverF1 n = F.run $
  Fr.runReader (0::Int) $
    Fs.runState (0::Integer) (fe n)

layerOverF2 n = F.run $
  Fr.runReader (0::Int) $
  Fr.runReader (0::Integer) $
    Fs.runState (0::Integer) (fe n)

layerOverF3 n = F.run $
  Fr.runReader (0::Int) $
  Fr.runReader (0::Integer) $
  Fr.runReader True $
    Fs.runState (0::Integer) (fe n)

layerOverF4 n = F.run $
  Fr.runReader (0::Int) $
  Fr.runReader (0::Integer) $
  Fr.runReader True $
  Fr.runReader "0" $
    Fs.runState (0::Integer) (fe n)

layerOverF5 n = F.run $
  Fr.runReader (0::Int) $
  Fr.runReader (0::Integer) $
  Fr.runReader True $
  Fr.runReader "0" $
  Fr.runReader 'c' $
    Fs.runState (0::Integer) (fe n)

layerOverF6 n = F.run $
  Fr.runReader (0::Int) $
  Fr.runReader (0::Integer) $
  Fr.runReader True $
  Fr.runReader "0" $
  Fr.runReader 'c' $
  Fr.runReader (True,True) $
    Fs.runState (0::Integer) (fe n)

-- LAYER UNDER

layerUnderF1 n = F.run $
  Fs.runState (0::Integer) $
    Fr.runReader (0::Int) $
    fe n

layerUnderF2 n = F.run $
  Fs.runState (0::Integer) $
    Fr.runReader (0::Int) $
    Fr.runReader (0::Integer) $
    fe n

layerUnderF3 n = F.run $
  Fs.runState (0::Integer) $
    Fr.runReader (0::Int) $
    Fr.runReader (0::Integer) $
    Fr.runReader True $
    fe n

layerUnderF4 n = F.run $
  Fs.runState (0::Integer) $
    Fr.runReader (0::Int) $
    Fr.runReader (0::Integer) $
    Fr.runReader True $
    Fr.runReader "0" $
    fe n

layerUnderF5 n = F.run $
  Fs.runState (0::Integer) $
    Fr.runReader (0::Int) $
    Fr.runReader (0::Integer) $
    Fr.runReader True $
    Fr.runReader "0" $
    Fr.runReader 'c' $
    fe n

layerUnderF6 n = F.run $
  Fs.runState (0::Integer) $
    Fr.runReader (0::Int) $
    Fr.runReader (0::Integer) $
    Fr.runReader True $
    Fr.runReader "0" $
    Fr.runReader 'c' $
    Fr.runReader (True,True) $
    fe n

-------------------------------------------------------
-- EFF
-------------------------------------------------------

eff :: (State Integer :? e) => Integer -> Eff e Integer
eff n = foldM f 1 [n, n-1 .. 0]
  where f acc x | x `mod` 5 == 0 = do n <- perform get ()
                                      perform put (n+1)
                                      return (max acc x)
        f acc x = return (max acc x)

layerEff n = runEff $
  state (0::Integer) (eff n)

layerOverEff1 n = runEff $
  reader (0::Int) $
    state (0::Integer) (eff n)

layerOverEff2 n = runEff $
  reader (0::Int) $
  reader (0::Integer) $
    state (0::Integer) (eff n)

layerOverEff3 n = runEff $
  reader (0::Int) $
  reader (0::Integer) $
  reader True $
    state (0::Integer) (eff n)

layerOverEff4 n = runEff $
  reader (0::Int) $
  reader (0::Integer) $
  reader True $
  reader "0" $
    state (0::Integer) (eff n)

layerOverEff5 n = runEff $
  reader (0::Int) $
  reader (0::Integer) $
  reader True $
  reader 'c' $
    state (0::Integer) (eff n)

layerOverEff6 n = runEff $
  reader (0::Int) $
  reader (0::Integer) $
  reader True $
  reader "0" $
  reader 'c' $
  reader (True,True) $
    state (0::Integer) (eff n)


layerUnderEff1 n = runEff $
  state (0::Integer) $
    reader (0::Int) $
    eff n

layerUnderEff2 n = runEff $
  state (0::Integer) $
    reader (0::Int) $
    reader (0::Integer) $
    eff n

layerUnderEff3 n = runEff $
  state (0::Integer) $
    reader (0::Int) $
    reader (0::Integer) $
    reader True $
    eff n

layerUnderEff4 n = runEff $
  state (0::Integer) $
    reader (0::Int) $
    reader (0::Integer) $
    reader True $
    reader "0" $
    eff n

layerUnderEff5 n = runEff $
  state (0::Integer) $
    reader (0::Int) $
    reader (0::Integer) $
    reader True $
    reader 'c' $
    eff n

layerUnderEff6 n = runEff $
  state (0::Integer) $
    reader (0::Int) $
    reader (0::Integer) $
    reader True $
    reader "0" $
    reader 'c' $
    reader (True,True) $
    eff n

-------------------------------------------------------
-- EFF NON TAIL
-------------------------------------------------------
stateNonTail :: a -> Eff (State a :* e) ans -> Eff e ans
stateNonTail init
  = handlerLocal init (State{ get = operation (\() k -> do{ x <- localGet; k x }),
                              put = operation (\x k  -> do{ localPut x; k () }) })

layerEffNonTail n = runEff $
  stateNonTail (0::Integer) (eff n)

layerOverEffNonTail1 n = runEff $
  reader (0::Int) $
    stateNonTail (0::Integer) (eff n)

layerOverEffNonTail2 n = runEff $
  reader (0::Int) $
  reader (0::Integer) $
    stateNonTail (0::Integer) (eff n)

layerOverEffNonTail3 n = runEff $
  reader (0::Int) $
  reader (0::Integer) $
  reader True $
    stateNonTail (0::Integer) (eff n)

layerOverEffNonTail4 n = runEff $
  reader (0::Int) $
  reader (0::Integer) $
  reader True $
  reader "0" $
    stateNonTail (0::Integer) (eff n)

layerOverEffNonTail5 n = runEff $
  reader (0::Int) $
  reader (0::Integer) $
  reader True $
  reader 'c' $
    stateNonTail (0::Integer) (eff n)

layerOverEffNonTail6 n = runEff $
  reader (0::Int) $
  reader (0::Integer) $
  reader True $
  reader "0" $
  reader 'c' $
  reader (True,True) $
    stateNonTail (0::Integer) (eff n)


layerUnderEffNonTail1 n = runEff $
  stateNonTail (0::Integer) $
    reader (0::Int) $
    eff n

layerUnderEffNonTail2 n = runEff $
  stateNonTail (0::Integer) $
    reader (0::Int) $
    reader (0::Integer) $
    eff n

layerUnderEffNonTail3 n = runEff $
  stateNonTail (0::Integer) $
    reader (0::Int) $
    reader (0::Integer) $
    reader True $
    eff n

layerUnderEffNonTail4 n = runEff $
  stateNonTail (0::Integer) $
    reader (0::Int) $
    reader (0::Integer) $
    reader True $
    reader "0" $
    eff n

layerUnderEffNonTail5 n = runEff $
  stateNonTail (0::Integer) $
    reader (0::Int) $
    reader (0::Integer) $
    reader True $
    reader 'c' $
    eff n

layerUnderEffNonTail6 n = runEff $
  stateNonTail (0::Integer) $
    reader (0::Int) $
    reader (0::Integer) $
    reader True $
    reader "0" $
    reader 'c' $
    reader (True,True) $
    eff n


{-
-------------------------------------------------------
-- Eff Linear
-------------------------------------------------------

effL :: (Linear (State Integer) :? e) => Integer -> Eff e Integer
effL n = foldM f 1 [n, n-1 .. 0]
      where f acc x | x `mod` 5 == 0 = do n <- lperform get ()
                                          lperform put (n+1)
                                          return (max acc x)
            f acc x = return (max acc x)

layerEffL n = runEff $ lstate (0::Integer) (effL n)

layerOverEffL1 n = runEff $
  lreader (0::Int) $
  lstate (0::Integer) (effL n)

layerOverEffL2 n = runEff $
  lreader (0::Int) $
  lreader (0::Integer) $
  lstate (0::Integer) (effL n)

layerOverEffL3 n = runEff $
  lreader (0::Int) $
  lreader (0::Integer) $
  lreader True $
  lstate (0::Integer) (effL n)

layerOverEffL4 n = runEff $
  lreader (0::Int) $
  lreader (0::Integer) $
  lreader True $
  lreader "0" $
  lstate (0::Integer) (effL n)

layerUnderEffL1 n = runEff $
  lstate (0::Integer) $
  lreader (0::Int) $
  effL n

layerUnderEffL2 n = runEff $
  lstate (0::Integer) $
  lreader (0::Int) $
  lreader (0::Integer) $
  effL n

layerUnderEffL3 n = runEff $
  lstate (0::Integer) $
  lreader (0::Int) $
  lreader (0::Integer) $
  lreader True $
  effL n

layerUnderEffL4 n = runEff $
  lstate (0::Integer) $
  lreader (0::Int) $
  lreader (0::Integer) $
  lreader True $
  lreader "0" $
  effL n
-}
-------------------------------------------------------
-- TEST
-------------------------------------------------------

quick = True

comp n = if (quick) then
         [ bench "pure 0"            $ whnf layerPure n
         , bench "runST 0"            $ whnf layerST n
         , bench "monadic 0"            $ whnf layerMonadic n
         , bench "eff 0"                $ whnf layerEff n
         , bench "fused effects 0"      $ whnf layerF n
         , bench "extensible effects 0" $ whnf layerEE n
         ]
         else 
         [ bench "monadic 0"          $ whnf layerMonadic n
         , bench "monadic over 1"     $ whnf layerOverMonadic1 n
         , bench "monadic over 2"     $ whnf layerOverMonadic2 n
         , bench "monadic over 3"     $ whnf layerOverMonadic3 n
         , bench "monadic over 4"     $ whnf layerOverMonadic4 n
         , bench "monadic over 5"     $ whnf layerOverMonadic5 n
         , bench "monadic over 6"     $ whnf layerOverMonadic6 n
         , bench "monadic under 1"    $ whnf layerUnderMonadic1 n
         , bench "monadic under 2"    $ whnf layerUnderMonadic2 n
         , bench "monadic under 3"    $ whnf layerUnderMonadic3 n
         , bench "monadic under 4"    $ whnf layerUnderMonadic4 n
         , bench "monadic under 5"    $ whnf layerUnderMonadic5 n
         , bench "monadic under 6"    $ whnf layerUnderMonadic6 n

         , bench "extensible effects 0"          $ whnf layerEE n
         , bench "extensible effects over 1"     $ whnf layerOverEE1 n
         , bench "extensible effects over 2"     $ whnf layerOverEE2 n
         , bench "extensible effects over 3"     $ whnf layerOverEE3 n
         , bench "extensible effects over 4"     $ whnf layerOverEE4 n
         , bench "extensible effects over 5"     $ whnf layerOverEE5 n
         , bench "extensible effects over 6"     $ whnf layerOverEE6 n
         , bench "extensible effects under 1"    $ whnf layerUnderEE1 n
         , bench "extensible effects under 2"    $ whnf layerUnderEE2 n
         , bench "extensible effects under 3"    $ whnf layerUnderEE3 n
         , bench "extensible effects under 4"    $ whnf layerUnderEE4 n
         , bench "extensible effects under 5"    $ whnf layerUnderEE5 n
         , bench "extensible effects under 6"    $ whnf layerUnderEE6 n

         , bench "fused effects 0"          $ whnf layerF n
         , bench "fused effects over 1"     $ whnf layerOverF1 n
         , bench "fused effects over 2"     $ whnf layerOverF2 n
         , bench "fused effects over 3"     $ whnf layerOverF3 n
         , bench "fused effects over 4"     $ whnf layerOverF4 n
         , bench "fused effects over 5"     $ whnf layerOverF5 n
         , bench "fused effects over 6"     $ whnf layerOverF6 n
         , bench "fused effects under 1"    $ whnf layerUnderF1 n
         , bench "fused effects under 2"    $ whnf layerUnderF2 n
         , bench "fused effects under 3"    $ whnf layerUnderF3 n
         , bench "fused effects under 4"    $ whnf layerUnderF4 n
         , bench "fused effects under 5"    $ whnf layerUnderF5 n
         , bench "fused effects under 6"    $ whnf layerUnderF6 n

{-
         , bench "eff linear 0"          $ whnf layerEffL n
         , bench "eff linear over 1"     $ whnf layerOverEffL1 n
         , bench "eff linear over 2"     $ whnf layerOverEffL2 n
         , bench "eff linear over 3"     $ whnf layerOverEffL3 n
         , bench "eff linear over 4"     $ whnf layerOverEffL4 n
         , bench "eff linear under 1"    $ whnf layerUnderEffL1 n
         , bench "eff linear under 2"    $ whnf layerUnderEffL2 n
         , bench "eff linear under 3"    $ whnf layerUnderEffL3 n
         , bench "eff linear under 4"    $ whnf layerUnderEffL4 n
-}

         , bench "eff 0"          $ whnf layerEff n
         , bench "eff over 1"     $ whnf layerOverEff1 n
         , bench "eff over 2"     $ whnf layerOverEff2 n
         , bench "eff over 3"     $ whnf layerOverEff3 n
         , bench "eff over 4"     $ whnf layerOverEff4 n
         , bench "eff over 5"     $ whnf layerOverEff5 n
         , bench "eff over 6"     $ whnf layerOverEff6 n
         , bench "eff under 1"    $ whnf layerUnderEff1 n
         , bench "eff under 2"    $ whnf layerUnderEff2 n
         , bench "eff under 3"    $ whnf layerUnderEff3 n
         , bench "eff under 4"    $ whnf layerUnderEff4 n
         , bench "eff under 5"    $ whnf layerUnderEff6 n
         , bench "eff under 6"    $ whnf layerUnderEff6 n

         , bench "eff nontail 0"          $ whnf layerEffNonTail n
         , bench "eff nontail over 1"     $ whnf layerOverEffNonTail1 n
         , bench "eff nontail over 2"     $ whnf layerOverEffNonTail2 n
         , bench "eff nontail over 3"     $ whnf layerOverEffNonTail3 n
         , bench "eff nontail over 4"     $ whnf layerOverEffNonTail4 n
         , bench "eff nontail over 5"     $ whnf layerOverEffNonTail5 n
         , bench "eff nontail over 6"     $ whnf layerOverEffNonTail6 n
         , bench "eff nontail under 1"    $ whnf layerUnderEffNonTail1 n
         , bench "eff nontail under 2"    $ whnf layerUnderEffNonTail2 n
         , bench "eff nontail under 3"    $ whnf layerUnderEffNonTail3 n
         , bench "eff nontail under 4"    $ whnf layerUnderEffNonTail4 n
         , bench "eff nontail under 5"    $ whnf layerUnderEffNonTail5 n
         , bench "eff nontail under 6"    $ whnf layerUnderEffNonTail6 n
         ]

num :: Integer
num = 10^6

main :: IO ()
main = defaultMain
       [ bgroup (show num) (comp num) ]
