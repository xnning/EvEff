{-# LANGUAGE
    FlexibleContexts
  , AllowAmbiguousTypes -- Extensible Effects
  , TypeOperators
#-}
module TestLayer where

import Criterion.Main
import Criterion.Types
import Control.Ev.Eff
import Control.Ev.Util

import Control.Monad (foldM)
import qualified Control.Monad.State as Ms
import qualified Control.Monad.Reader as Mr

-- Extensible Effects
import qualified Control.Eff as EE
import qualified Control.Eff.State.Lazy as EEs
import qualified Control.Eff.Reader.Lazy as EEr

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

-- LAYER UNDER

layrunEffderMonadic1 n =
    flip Ms.runState 0 $
     flip Mr.runReaderT (0::Int) $
      monadic n

layrunEffderMonadic2 n =
    flip Ms.runState 0 $
     flip Mr.runReaderT (0::Int) $
     flip Mr.runReaderT (0::Integer) $
      monadic n

layrunEffderMonadic3 n =
    flip Ms.runState 0 $
     flip Mr.runReaderT (0::Int) $
     flip Mr.runReaderT (0::Integer) $
     flip Mr.runReaderT True $
      monadic n

layrunEffderMonadic4 n =
    flip Ms.runState 0 $
     flip Mr.runReaderT (0::Int) $
     flip Mr.runReaderT (0::Integer) $
     flip Mr.runReaderT True $
     flip Mr.runReaderT "0" $
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

-- LAYER UNDER

layrunEffderEE1 n = EE.run $
  EEs.runState (0::Integer) $
    EEr.runReader (0::Int) $
    ee n

layrunEffderEE2 n = EE.run $
  EEs.runState (0::Integer) $
    EEr.runReader (0::Int) $
    EEr.runReader (0::Integer) $
    ee n

layrunEffderEE3 n = EE.run $
  EEs.runState (0::Integer) $
    EEr.runReader (0::Int) $
    EEr.runReader (0::Integer) $
    EEr.runReader True $
    ee n

layrunEffderEE4 n = EE.run $
  EEs.runState (0::Integer) $
    EEr.runReader (0::Int) $
    EEr.runReader (0::Integer) $
    EEr.runReader True $
    EEr.runReader "0" $
    ee n

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

layrunEffderEff1 n = runEff $
  state (0::Integer) $
    reader (0::Int) $
    eff n

layrunEffderEff2 n = runEff $
  state (0::Integer) $
    reader (0::Int) $
    reader (0::Integer) $
    eff n

layrunEffderEff3 n = runEff $
  state (0::Integer) $
    reader (0::Int) $
    reader (0::Integer) $
    reader True $
    eff n

layrunEffderEff4 n = runEff $
  state (0::Integer) $
    reader (0::Int) $
    reader (0::Integer) $
    reader True $
    reader "0" $
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

layrunEffderEffNonTail1 n = runEff $
  stateNonTail (0::Integer) $
    reader (0::Int) $
    eff n

layrunEffderEffNonTail2 n = runEff $
  stateNonTail (0::Integer) $
    reader (0::Int) $
    reader (0::Integer) $
    eff n

layrunEffderEffNonTail3 n = runEff $
  stateNonTail (0::Integer) $
    reader (0::Int) $
    reader (0::Integer) $
    reader True $
    eff n

layrunEffderEffNonTail4 n = runEff $
  stateNonTail (0::Integer) $
    reader (0::Int) $
    reader (0::Integer) $
    reader True $
    reader "0" $
    eff n


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

-------------------------------------------------------
-- TEST
-------------------------------------------------------

comp n = [ bench "monadic 0"          $ whnf layerMonadic n
         , bench "monadic over 1"     $ whnf layerOverMonadic1 n
         , bench "monadic over 2"     $ whnf layerOverMonadic2 n
         , bench "monadic over 3"     $ whnf layerOverMonadic3 n
         , bench "monadic over 4"     $ whnf layerOverMonadic4 n
         , bench "monadic under 1"    $ whnf layrunEffderMonadic1 n
         , bench "monadic under 2"    $ whnf layrunEffderMonadic2 n
         , bench "monadic under 3"    $ whnf layrunEffderMonadic3 n
         , bench "monadic under 4"    $ whnf layrunEffderMonadic4 n

         , bench "extensible effects 0"          $ whnf layerEE n
         , bench "extensible effects over 1"     $ whnf layerOverEE1 n
         , bench "extensible effects over 2"     $ whnf layerOverEE2 n
         , bench "extensible effects over 3"     $ whnf layerOverEE3 n
         , bench "extensible effects over 4"     $ whnf layerOverEE4 n
         , bench "extensible effects under 1"    $ whnf layrunEffderEE1 n
         , bench "extensible effects under 2"    $ whnf layrunEffderEE2 n
         , bench "extensible effects under 3"    $ whnf layrunEffderEE3 n
         , bench "extensible effects under 4"    $ whnf layrunEffderEE4 n

         , bench "eff linear 0"          $ whnf layerEffL n
         , bench "eff linear over 1"     $ whnf layerOverEffL1 n
         , bench "eff linear over 2"     $ whnf layerOverEffL2 n
         , bench "eff linear over 3"     $ whnf layerOverEffL3 n
         , bench "eff linear over 4"     $ whnf layerOverEffL4 n
         , bench "eff linear under 1"    $ whnf layerUnderEffL1 n
         , bench "eff linear under 2"    $ whnf layerUnderEffL2 n
         , bench "eff linear under 3"    $ whnf layerUnderEffL3 n
         , bench "eff linear under 4"    $ whnf layerUnderEffL4 n

         , bench "eff 0"          $ whnf layerEff n
         , bench "eff over 1"     $ whnf layerOverEff1 n
         , bench "eff over 2"     $ whnf layerOverEff2 n
         , bench "eff over 3"     $ whnf layerOverEff3 n
         , bench "eff over 4"     $ whnf layerOverEff4 n
         , bench "eff under 1"    $ whnf layrunEffderEff1 n
         , bench "eff under 2"    $ whnf layrunEffderEff2 n
         , bench "eff under 3"    $ whnf layrunEffderEff3 n
         , bench "eff under 4"    $ whnf layrunEffderEff4 n

         , bench "eff nontail 0"          $ whnf layerEffNonTail n
         , bench "eff nontail over 1"     $ whnf layerOverEffNonTail1 n
         , bench "eff nontail over 2"     $ whnf layerOverEffNonTail2 n
         , bench "eff nontail over 3"     $ whnf layerOverEffNonTail3 n
         , bench "eff nontail over 4"     $ whnf layerOverEffNonTail4 n
         , bench "eff nontail under 1"    $ whnf layrunEffderEffNonTail1 n
         , bench "eff nontail under 2"    $ whnf layrunEffderEffNonTail2 n
         , bench "eff nontail under 3"    $ whnf layrunEffderEffNonTail3 n
         , bench "eff nontail under 4"    $ whnf layrunEffderEffNonTail4 n
         ]

num :: Integer
num = 10^6

main :: IO ()
main = defaultMain
       [ bgroup (show num) (comp num) ]
