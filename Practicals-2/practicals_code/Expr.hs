{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Replace case with maybe" #-}
import MiniPrelude hiding ((>>=))
import Prelude ()

data Expr
  = Num Int
  | Neg Expr
  | Add Expr Expr
  | Div Expr Expr
  deriving (Show)

e1 = Add (Num 3) (Div (Num 2) (Neg (Num 0)))
e2 = Neg (Num 0)

eval :: Expr -> Maybe Int
eval (Num x) = Just x
eval (Add e0 e1) = case eval e0 of
  Just v0 -> case eval e1 of
    Just v1 -> Just (v0 + v1)
    Nothing -> Nothing
  Nothing -> Nothing
eval (Neg e) = case eval e of
  Just v -> Just (negate v)
  Nothing -> Nothing
eval (Div e0 e1) = case eval e0 of
  Just v0 -> case eval e1 of
    Just 0 -> Nothing
    Just v1 -> Just (v0 `div` v1)
    Nothing -> Nothing
  Nothing -> Nothing

(>>=) :: Maybe t -> (t -> Maybe a) -> Maybe a
mx >>= f = case mx of
  Just v -> f v
  Nothing -> Nothing

evalBind :: Expr -> Maybe Int
evalBind (Num n) = Just n
evalBind (Neg e) =
  evalBind e >>= \v -> Just (negate v)
evalBind (Add e0 e1) =
  evalBind e0 >>= \v0 ->
    evalBind e1 >>= \v1 ->
      Just (v0 + v1)
evalBind (Div e0 e1) =
  evalBind e0 >>= \v0 ->
    evalBind e1 >>= \v1 ->
      if v1 == 0
        then Nothing
        else Just (v0 `div` v1)
