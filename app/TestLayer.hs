{-# LANGUAGE
    FlexibleContexts
  , AllowAmbiguousTypes -- Extensible Effects
  , TypeOperators
#-}
module TestLayer where

import Criterion.Main
import Criterion.Types
import EffEvScoped
import Library hiding (main)

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

-------------------------------------------------------
-- EFF
-------------------------------------------------------

eff :: (State Integer :? e) => Integer -> Eff e Integer
eff n = foldM f 1 [n, n-1 .. 0]
  where f acc x | x `mod` 5 == 0 = do n <- get
                                      put (n+1)
                                      return (max acc x)
        f acc x = return (max acc x)

layerEff n = erun $
  lstate (0::Integer) (eff n)

layerOverEff1 n = erun $
  reader (0::Int) $
    lstate (0::Integer) (eff n)

layerOverEff2 n = erun $
  reader (0::Int) $
  reader (0::Integer) $
    lstate (0::Integer) (eff n)

layerOverEff3 n = erun $
  reader (0::Int) $
  reader (0::Integer) $
  reader True $
    lstate (0::Integer) (eff n)

layerOverEff4 n = erun $
  reader (0::Int) $
  reader (0::Integer) $
  reader True $
  reader "0" $
    lstate (0::Integer) (eff n)

layerUnderEff1 n = erun $
  lstate (0::Integer) $
    reader (0::Int) $
    eff n

layerUnderEff2 n = erun $
  lstate (0::Integer) $
    reader (0::Int) $
    reader (0::Integer) $
    eff n

layerUnderEff3 n = erun $
  lstate (0::Integer) $
    reader (0::Int) $
    reader (0::Integer) $
    reader True $
    eff n

layerUnderEff4 n = erun $
  lstate (0::Integer) $
    reader (0::Int) $
    reader (0::Integer) $
    reader True $
    reader "0" $
    eff n

-------------------------------------------------------
-- EFF NON TAIL
-------------------------------------------------------

layerEffNonTail n = erun $
  lstateNonTail (0::Integer) (eff n)

layerOverEffNonTail1 n = erun $
  reader (0::Int) $
    lstateNonTail (0::Integer) (eff n)

layerOverEffNonTail2 n = erun $
  reader (0::Int) $
  reader (0::Integer) $
    lstateNonTail (0::Integer) (eff n)

layerOverEffNonTail3 n = erun $
  reader (0::Int) $
  reader (0::Integer) $
  reader True $
    lstateNonTail (0::Integer) (eff n)

layerOverEffNonTail4 n = erun $
  reader (0::Int) $
  reader (0::Integer) $
  reader True $
  reader "0" $
    lstateNonTail (0::Integer) (eff n)

layerUnderEffNonTail1 n = erun $
  lstateNonTail (0::Integer) $
    reader (0::Int) $
    eff n

layerUnderEffNonTail2 n = erun $
  lstateNonTail (0::Integer) $
    reader (0::Int) $
    reader (0::Integer) $
    eff n

layerUnderEffNonTail3 n = erun $
  lstateNonTail (0::Integer) $
    reader (0::Int) $
    reader (0::Integer) $
    reader True $
    eff n

layerUnderEffNonTail4 n = erun $
  lstateNonTail (0::Integer) $
    reader (0::Int) $
    reader (0::Integer) $
    reader True $
    reader "0" $
    eff n

-------------------------------------------------------
-- TEST
-------------------------------------------------------

comp n = [ bench "monadic 0"          $ whnf layerMonadic n
         , bench "monadic over 1"     $ whnf layerOverMonadic1 n
         , bench "monadic over 2"     $ whnf layerOverMonadic2 n
         , bench "monadic over 3"     $ whnf layerOverMonadic3 n
         , bench "monadic over 4"     $ whnf layerOverMonadic4 n
         , bench "monadic under 1"    $ whnf layerUnderMonadic1 n
         , bench "monadic under 2"    $ whnf layerUnderMonadic2 n
         , bench "monadic under 3"    $ whnf layerUnderMonadic3 n
         , bench "monadic under 4"    $ whnf layerUnderMonadic4 n

         , bench "extensive effects 0"          $ whnf layerEE n
         , bench "extensive effects over 1"     $ whnf layerOverEE1 n
         , bench "extensive effects over 2"     $ whnf layerOverEE2 n
         , bench "extensive effects over 3"     $ whnf layerOverEE3 n
         , bench "extensive effects over 4"     $ whnf layerOverEE4 n
         , bench "extensive effects under 1"    $ whnf layerUnderEE1 n
         , bench "extensive effects under 2"    $ whnf layerUnderEE2 n
         , bench "extensive effects under 3"    $ whnf layerUnderEE3 n
         , bench "extensive effects under 4"    $ whnf layerUnderEE4 n

         , bench "eff 0"          $ whnf layerEff n
         , bench "eff over 1"     $ whnf layerOverEff1 n
         , bench "eff over 2"     $ whnf layerOverEff2 n
         , bench "eff over 3"     $ whnf layerOverEff3 n
         , bench "eff over 4"     $ whnf layerOverEff4 n
         , bench "eff under 1"    $ whnf layerUnderEff1 n
         , bench "eff under 2"    $ whnf layerUnderEff2 n
         , bench "eff under 3"    $ whnf layerUnderEff3 n
         , bench "eff under 4"    $ whnf layerUnderEff4 n

         , bench "eff nontail 0"          $ whnf layerEffNonTail n
         , bench "eff nontail over 1"     $ whnf layerOverEffNonTail1 n
         , bench "eff nontail over 2"     $ whnf layerOverEffNonTail2 n
         , bench "eff nontail over 3"     $ whnf layerOverEffNonTail3 n
         , bench "eff nontail over 4"     $ whnf layerOverEffNonTail4 n
         , bench "eff nontail under 1"    $ whnf layerUnderEffNonTail1 n
         , bench "eff nontail under 2"    $ whnf layerUnderEffNonTail2 n
         , bench "eff nontail under 3"    $ whnf layerUnderEffNonTail3 n
         , bench "eff nontail under 4"    $ whnf layerUnderEffNonTail4 n
         ]

num :: Integer
num = 10^6

main :: IO ()
main = defaultMain
       [ bgroup (show num) (comp num) ]
