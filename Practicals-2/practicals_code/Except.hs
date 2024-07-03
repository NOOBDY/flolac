{-# OPTIONS_GHC -Wno-noncanonical-monad-instances #-}

import MiniPrelude hiding (catchE)
import Prelude ()

data Expr = Num Int | Add Expr Expr | Div Expr Expr
  deriving (Show)

data Except e a = Return a | Throw e
  deriving (Show)

catchE :: Except e a -> (e -> Except e a) -> Except e a
catchE (Return a) f = Return a
catchE (Throw e) f = f e

data Err = DivByZero | Overflow | Underflow
  deriving (Show)

instance Monad (Except e) where
  return = Return
  Return x >>= f = f x
  Throw err >>= f = Throw err

eval :: Expr -> Except Err Int
eval e = catchE (eval' e) handler
 where
  handler Overflow = return 32767
  handler Underflow = return (-32768)
  handler DivByZero = Throw DivByZero

eval' :: Expr -> Except Err Int
eval' (Num e) = Return e
eval' (Add e0 e1) =
  eval e0 >>= \v0 ->
    eval e1 >>= \v1 ->
      v0 `add` v1
eval' (Div e0 e1) =
  eval e0 >>= \v0 ->
    eval e1 >>= \v1 ->
      if v1 == 0
        then Throw DivByZero
        else v0 `div'` v1

-- use add and div' instead of (+) and div
-- call eval somewhere

tstExpr00, tstExpr01 :: Expr
tstExpr00 =
  (Num 65536 `Add` Num 32768)
    `Div` (Num 1 `Add` Num 65536)
tstExpr01 = (Num 32768 `Div` Num 0) `Add` Num 32768

-- eval tstExpr00  ===> Return 1
-- eval tstExpr01  ===> Throw DivByZero

-- "primitive" addition and division that raise
-- overflow and underflow errors.
-- add and div' are to be used in place of (+) and div.

overflow :: Int -> Bool
overflow n = n > 32767

underflow :: Int -> Bool
underflow n = n < -32768

flowcheck :: Int -> Except Err Int
flowcheck n
  | overflow n = Throw Overflow
  | underflow n = Throw Underflow
  | otherwise = return n

add :: Int -> Int -> Except Err Int
add x y = flowcheck (x + y)

div' :: Int -> Int -> Except Err Int
div' x y = flowcheck (x `div` y)

-- Functor and Applicative instances

instance Functor (Except e) where
  fmap = liftM

instance Applicative (Except e) where
  pure = return
  (<*>) = ap
