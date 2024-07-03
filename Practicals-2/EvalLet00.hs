{-# HLINT ignore "Use newtype instead of data" #-}
{-# OPTIONS_GHC -Wno-noncanonical-monad-instances #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Avoid lambda" #-}
{-# HLINT ignore "Use id" #-}
{-# HLINT ignore "Use const" #-}

import MiniPrelude hiding (MonadReader (..))
import Prelude ()

data Expr
  = Num Int
  | Neg Expr
  | Add Expr Expr
  | Var Name
  | Let Name Expr Expr

type Name = String

type Env = List (Name, Int)

-- What if we define
-- type Env = Name -> Maybe Int   --?

-- The function
--   lookup :: Eq a => a -> [(a, b)] -> Maybe b
-- is defined in GHC.List and imported here.

-- eval :: Expr -> Env -> Int
-- eval (Num n) env = n
-- eval (Neg e) env = negate (eval e env)
-- eval (Add e0 e1) env = eval e0 env + eval e1 env
-- eval (Var x) env =
--   case lookup x env of
--     Just v -> v
--     Nothing -> error "panic"
-- eval (Let x e0 e1) env = eval e1 ((x, eval e0 env) : env)

eval :: Expr -> Reader Env Int
eval (Num n) = return n
-- eval (Neg e) = eval e >>= \v -> return (negate v)
eval (Neg e) = negate <$> eval e
eval (Add e0 e1) =
  do
    v0 <- eval e0
    v1 <- eval e1
    return (v0 + v1)
--   eval e0 >>= \v0 ->
--     eval e1 >>= \v1 ->
--       return (v0 + v1)
eval (Var x) =
  ask >>= \env ->
    case lookup x env of
      Just v -> return v
eval (Let x e0 e1) =
  eval e0 >>= \v0 ->
    local (\env -> (x, v0) : env) (eval e1)

tstExpr00 :: Expr
tstExpr00 =
  Let
    "x"
    (Num 3)
    ( Add
        ( Add
            (Var "x")
            ( Let
                "x"
                (Num 4)
                (Var "x")
            )
        )
        (Neg (Var "x"))
    )

--

data Reader e a = Rdr (e -> a)

runReader :: Reader e a -> e -> a
runReader (Rdr f) = f

instance Monad (Reader e) where
  return x = Rdr (\env -> x)
  Rdr mx >>= f = Rdr (\env -> runReader (f (mx env)) env)

ask :: Reader e e
ask = Rdr (\env -> env)

local :: (e -> e) -> Reader e a -> Reader e a
local f mx = Rdr (\env -> runReader mx (f env))

-- Functor and Applicative instances

instance Functor (Reader e) where
  fmap = liftM

instance Applicative (Reader e) where
  pure = return
  (<*>) = ap
