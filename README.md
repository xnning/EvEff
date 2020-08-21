# EvEff: Efficient effect handlers based on Evidence translation

Efficient effect handlers based on evidence translation [1]. 
The interface and design is described in detail in 
"[_Effect Handlers in Haskell, Evidently_](https://www.microsoft.com/en-us/research/publication/effect-handlers-in-haskell-evidently)", 
Ningning Xie and Daan Leijen, Haskell 2020.

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
          return s
```

Enjoy,  
  Daan Leijen and Ningning Xie,  May 2020.


[1] "_Effect Handlers, Evidently_", Ningning Xie _et al._, ICFP 2020  [(pdf)](https://www.microsoft.com/en-us/research/publication/effect-handlers-evidently).
