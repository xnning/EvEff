# EvEff: Efficient effect handlers based on Evidence translation

Efficient effect handlers based on Evidence translation. The implementation
is based on /"Effect Handlers, Evidently"/, Ningning Xie /et al./, ICFP 2020 
[(pdf)](https://www.microsoft.com/en-us/research/publication/effect-handlers-evidently),
and the interface and design is described in detail in 
/"Effect Handlers in Haskell, Evidently"/, Ningning Xie and Daan Leijen, Haskell 2020 
[(pdf)](https://www.microsoft.com/en-us/research/publication/effect-handlers-in-haskell-evidently).

Installation:

* First install [stack](https://docs.haskellstack.org)
* Build with `> stack build`
* Load examples:
  ```
  > stack ghci eveff:lib
  ..
  ghci> runEff helloWorld
  "hello world" 
  ```

An example of defining and using a `Reader` effect:

```Haskell
{-# LANGUAGE  TypeOperators, FlexibleContexts, Rank2Types #-}
import Control.Ev.Eff

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
```

Enjoy,  
  Daan Leijen and Ningning Xie,  May 2020.
