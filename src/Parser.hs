{-# LANGUAGE  TypeOperators, FlexibleContexts, Rank2Types  #-}
-- Nice Examples for the paper
import EffEvScopedOP
import Prelude hiding (flip, fail)
import Data.Char

operation op = opNormal op
function f   = opTail f
value x      = function (\() -> return x)

handler h action
  = handle h action
handlerRet f h action
  = handler h (do x <- action; return (f x))

handlerLocal :: a -> (Local a -> h e ans) -> Eff (h :* e) ans -> Eff e ans
handlerLocal init hcreate action
    = local init (\loc -> handle (hcreate loc) action)

handlerLocalRet :: a -> (b -> a -> ans) -> (Local a -> h e ans) -> Eff (h :* e) b -> Eff e ans
handlerLocalRet init ret hcreate action
    = local init (\loc -> handle (hcreate loc) (do x <- action; l <- localGet loc init; return (ret x l)))

data Many e ans = Many { flip :: Op () Bool e ans
                       , fail :: forall a. Op () a e ans
                       }

choice :: Many :? e => Eff e a -> Eff e a -> Eff e a
choice p1 p2 = do b <- perform flip ()
                  if b then p1
                  else p2

many :: Many :? e => (() -> Eff e a) -> Eff e [a]
many p = choice (many1 p) (return [])

many1 :: Many :? e => (() -> Eff e a) -> Eff e [a]
many1 p = do x <- p ()
             xs <- many p
             return (x:xs)

solutions :: Eff (Many :* e) a -> Eff e [a]
solutions
  = handlerRet (\x -> [x])
    Many{ fail = operation (\_ _ -> return [])
        , flip = operation (\_ k -> do xs <- k True
                                       ys <- k False
                                       return (xs ++ ys))
        }

eager :: Eff (Many :* e) a -> Eff e (Maybe a)
eager = handlerRet (\x -> Just x)
        Many{ fail = operation (\_ _ -> return Nothing)
            , flip = operation (\_ k -> do x <- k True
                                           case x of
                                             Nothing -> k False
                                             Just _  -> return x)
            }

data Parse e ans = Parse { satisfy :: forall a. Op (String -> (Maybe (a, String))) a e ans}

parse :: Many :? e => String -> Eff (Parse :* e) b -> Eff e (b, String)
parse init = handlerLocalRet init
                 (\x y -> (x, y))
                 (\loc -> Parse { satisfy = operation $
                                             \p k -> do input <- localGet loc p
                                                        case (p input) of
                                                           Nothing -> perform fail ()
                                                           Just (x, rest) -> do localSet loc rest
                                                                                k x
                                })


symbol :: Parse :? e => Char -> Eff e Char
symbol c = perform satisfy (\input ->
                              case input of
                                (d:rest) | d == c -> Just (c, rest)
                                _ -> Nothing
                                )

digit :: Parse :? e => () -> Eff e Int
digit c = perform satisfy (\input ->
                              case input of
                                (d:rest) | isDigit d -> Just (digitToInt d, rest)
                                _ -> Nothing
                                )

number :: (Parse :? e, Many :? e) => Eff e Int
number = do xs <- many1 digit
            return $ foldl (\n d -> 10 * n + d) 0 xs

expr :: (Parse :? e, Many :? e) => Eff e Int
expr = choice (do i <- term
                  symbol '+'
                  j <- term
                  return (i + j))
              term

term :: (Parse :? e, Many :? e) => Eff e Int
term = choice (do i <- factor
                  symbol '*'
                  j <- factor
                  return (i * j))
              factor

factor :: (Parse :? e, Many :? e) => Eff e Int
factor = choice number
                (do symbol '('
                    i <- expr
                    symbol ')'
                    return i)

test1 = erun $ solutions $ parse "1+2*3" expr

test2 = erun $ eager $ parse "1+2*3" expr
