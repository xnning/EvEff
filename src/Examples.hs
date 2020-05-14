{-# LANGUAGE  TypeOperators, FlexibleContexts, Rank2Types  #-}
-- Nice Examples for the paper
module Examples where
import Control.Ev.Eff
import Prelude hiding (flip)
import Data.Char
import Data.Maybe

-- BEGIN:reader
data Reader a e ans = Reader { ask :: Op () a e ans }
-- END:reader

-- BEGIN:readerhr
hr :: a -> Reader a e ans  
hr x = Reader{ ask = operation (\ () k -> k x) } 
-- END:readerhr

-- BEGIN:readerh
reader :: a -> Eff (Reader a :* e) ans -> Eff e ans  
reader x action = handler (hr x) action
-- END:readerh

-- when to introduce function
-- show type of: handler :: h e ans -> Eff (h :* e) -> Eff e

-- BEGIN:readerex1
sample1 = reader "world" $
          do s <- perform ask ()
             return ("hello " ++ s)
-- END:readerex1

-- BEGIN:readermult
greetOrExit :: (Reader String :? e, Reader Bool :? e)  
   => Eff e String
greetOrExit
  = do s <- perform ask ()
       isExit <- perform ask ()
       if isExit then return ("goodbye " ++ s)
       else return ("hello " ++ s)
-- END:readermult

-- BEGIN:readernoctx
greetMaybe :: Reader String :? e => Eff e (Maybe String)    
greetMaybe = do s <- perform ask ()
                if null s then return Nothing
                else return (Just ("hello " ++ s))
-- END:readernoctx

-- BEGIN:readergreet
greet :: (Reader String :? e) => Eff e String  
greet = do s <- perform ask ()
           return ("hello " ++ s)
-- END:readergreet

-- BEGIN:readerex
helloWorld :: Eff e String   
helloWorld = reader "world" greet
-- END:readerex

-- BEGIN:exn
data Exn e ans
     = Exn { failure :: forall a. Op () a e ans }  
-- END:exn

-- BEGIN:toMaybe
toMaybe :: Eff (Exn :* e) a -> Eff e (Maybe a)    
toMaybe action
  = handlerRet Just (Exn{ failure = operation (\ () _ -> return Nothing) })
-- END:toMaybe

-- BEGIN:exceptDefault
exceptDefault :: a -> Eff (Exn :* e) a -> Eff e a  
exceptDefault x 
  = handler (Exn{ failure = operation (\ () _ -> return x) })
-- END:exceptDefault

-- BEGIN:exnex
safeDiv :: (Exn :? e) => Int -> Int -> Eff e Int  
safeDiv x 0 = perform failure ()
safeDiv x y = return (x `div` y)
-- END:exnex

safeHead :: (Exn :? e) => String -> Eff e Char  
safeHead []    = perform failure ()
safeHead (x:_) = return x

sample3 = reader "" $
          toMaybe $
          do s <- perform ask ()
             c <- safeHead s
             return (Just c)

-- introduce handlerRet

-- BEGIN:state
data State a e ans = State { get :: Op () a e ans  
                           , put :: Op a () e ans }
-- END:state

-- BEGIN:statex
state :: a -> Eff (State a :* e) ans -> Eff e ans  
state init = handlerLocal init $
             State{ get = function (\ () -> perform lget ())
                  , put = function (\ x  -> perform lput x) }
-- END:statex

-- BEGIN:statemon
local :: a -> Eff (Local a :* e) ans -> Eff e ans  
local init action
  = do f <- handler (Local { lget = operation (\ () k -> return $ 
                                                         \s -> do{ r <- k s; r s } )
                           , lput = operation (\ s k -> return $ 
                                                         \_ -> do{ r <- k (); r s } )
                           })
                    (do x <- action
                        return (\s -> return x))
       f init
-- END:statemon

-- BEGIN:stateex
add :: (State Int :? e) => Int -> Eff e ()  
add i = do j <- perform get ()
           perform put (i + j)
-- END:stateex

-- BEGIN:invert
invert :: (State Bool :? e) => Eff e Bool  
invert = do b <- perform get ()
            perform put (not b)
            perform get ()
-- END:invert

-- BEGIN:double
test :: Eff e Bool  
test = state True $ do invert
                       b <- perform get ()
                       return b
-- END:double

adder = state (1::Int) $
        do add 41
           i <- perform get ()
           return ("the final state is: " ++ show (i::Int))




-- BEGIN:output
data Output e ans = Output { out :: Op String () e ans }  

output :: Eff (Output :* e) ans -> Eff e (ans,String)  
output
  = handlerLocalRet [] (\x ss -> (x,concat ss)) $
    Output { out = function (\x -> localModify (x:)) }

-- END:output


-- BEGIN:amb
data Amb e ans
     = Amb { flip :: forall b. Op () Bool e ans }  
-- END:amb

-- BEGIN:xor
xor :: Amb :? e => Eff e Bool  
xor = do x <- perform flip ()
         y <- perform flip ()
         return ((x && not y) || (not x && y))
-- END:xor

-- BEGIN:allresults
allResults :: Eff (Amb :* e) a -> Eff e [a]  
allResults = handlerRet (\x -> [x]) Amb{
  flip = operation (\ () k ->
            do xs <- k True
               ys <- k False
               return (xs ++ ys)) }
-- END:allresults

-- BEGIN:backtrack
firstResult :: Eff (Amb :* e) (Maybe a)   
  -> Eff e (Maybe a)
firstResult = handler Amb{
  flip = operation (\ () k ->
           do xs <- k True
              case xs of
                Just _  -> return xs
                Nothing -> k False) }
-- END:backtrack



-- BEGIN:solutions
solutions :: Eff (Exn :* Amb :* e) a -> Eff e [a]  
solutions action
  = fmap catMaybes (allResults (toMaybe (action)))
-- END:solutions

-- BEGIN:eager
eager :: Eff (Exn :* Amb :* e) a -> Eff e (Maybe a)  
eager action = firstResult (toMaybe (action))
-- END:eager

-- BEGIN:choice
choice :: Amb :? e => Eff e a -> Eff e a -> Eff e a  
choice p1 p2 = do b <- perform flip ()
                  if b then p1 else p2
-- END:choice

-- BEGIN:manyeg
many :: Amb :? e => (() -> Eff e a) -> Eff e [a]  
many p = choice (many1 p) (return [])

many1 :: Amb :? e => (() -> Eff e a) -> Eff e [a]  
many1 p = do x <- p (); xs <- many p ; return (x:xs)
-- END:manyeg

-- BEGIN:parse
data Parse e ans = Parse {
  satisfy :: forall a.
        Op (String -> (Maybe (a, String))) a e ans }  
-- END:parse

-- BEGIN:parsefun
parse :: Exn :? e =>
  String -> Eff (Parse :* e) b -> Eff e (b, String)  
parse input
  = handlerLocalRet input (\x y -> (x, y)) $
    Parse { satisfy = operation $ \p k ->
      do input <- localGet
         case (p input) of
            Nothing -> perform failure ()
            Just (x, rest) -> do localPut rest
                                 k x }
-- END:parsefun

-- BEGIN:symbol
symbol :: Parse :? e => Char -> Eff e Char
symbol c = perform satisfy (\input -> case input of
    (d:rest) | d == c -> Just (c, rest)
    _ -> Nothing)

digit :: Parse :? e => () -> Eff e Int  
digit c = perform satisfy (\input -> case input of
    (d:rest) | isDigit d -> Just (digitToInt d, rest)
    _ -> Nothing)
-- END:symbol

-- BEGIN:expr
expr :: (Parse :? e, Amb :? e) => Eff e Int  
expr = choice (do i <- term; symbol '+'; j <- term
                  return (i + j))
              term

term :: (Parse :? e, Amb :? e) => Eff e Int  
term = choice (do i <- factor; symbol '*'; j <- factor
                  return (i * j))
              factor

factor :: (Parse :? e, Amb :? e) => Eff e Int  
factor = choice (do symbol '('; i <- expr; symbol ')'
                    return i)
                number

number :: (Parse :? e, Amb :? e) => Eff e Int  
number = do xs <- many1 digit
            return $ foldl (\n d -> 10 * n + d) 0 xs

-- END:expr

test1 = runEff (solutions (parse "1+2*3" expr))
-- [(7,""),(3,"*3"),(1,"+2*3")]

test2 = runEff (eager (parse "1+2*3" expr))
-- Just (7,"")
