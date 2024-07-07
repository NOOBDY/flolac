{-# HLINT ignore "Use newtype instead of data" #-}
{-# OPTIONS_GHC -Wno-noncanonical-monad-instances #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Avoid lambda" #-}

import MiniPrelude
import Prelude ()

data Expr
  = Num Int
  | Neg Expr
  | Add Expr Expr
  | Div Expr Expr
  | Var Name
  | Let Name Expr Expr
  deriving (Show)

data Except err a = Return a | Throw err
  deriving (Show)

data Err = DivByZero | VarNotFound Name
  deriving (Show)

type Name = String

type Env = [(Name, Int)]

-- What if we define
-- type Env = Name -> Maybe Int

-- The function
--   lookup :: Eq a => a -> [(a, b)] -> Maybe b
-- is defined in GHC.List and imported here.

eval :: Expr -> EvalMonad Int -- what's its type?
eval e = catchE (eval' e) handler
 where
  eval' :: Expr -> EvalMonad Int
  eval' (Num n) = return n
  eval' (Neg e) = eval e >>= \v -> return (negate v)
  eval' (Add e0 e1) = do
    v0 <- eval e0
    v1 <- eval e1
    return (v0 + v1)
  eval' (Div e0 e1) = do
    v0 <- eval e0
    v1 <- eval e1
    if v1 /= 0
      then return (v0 `div` v1)
      else throw DivByZero
  eval' (Var x) = do
    env <- ask
    case lookup x env of
      Just v -> return v
      Nothing -> throw (VarNotFound x)
  eval' (Let x e0 e1) = do
    v <- eval e0
    local (\env -> (x, v) : env) (eval e1)

  handler :: Err -> EvalMonad Int
  handler DivByZero = throw DivByZero
  handler (VarNotFound x) = undefined -- ! I forgor

instance Show (EvalMonad Int) where
  show (RE mx) = show (mx [])

tstExpr00 :: Expr
tstExpr00 =
  Let
    "x"
    (Num 3)
    ( Add
        ( Add
            (Var "x")
            (Let "x" (Num 4) (Var "x"))
        )
        (Neg (Var "x"))
    )

--

-- ReaderExcept
data ReEx env err a = RE (env -> Except err a)

type EvalMonad = ReEx Env Err

-- runReEx :: RE (env -> Except err a) -> env -> Except err a
runReEx :: ReEx env err a -> env -> Except err a
runReEx (RE f) = f

instance Monad (ReEx env err) where
  return x = RE (\env -> Return x)
  (>>=) (RE mx) f =
    RE
      ( \env -> case mx env of
          Return a -> runReEx (f a) env
          Throw err -> Throw err
      )

instance MonadReader env (ReEx env err) where
  ask = RE (\env -> Return env)
  local f re = RE (\env -> runReEx re (f env))

instance MonadExcept err (ReEx env err) where
  throw err = RE (\env -> Throw err)
  catchE (RE mx) f =
    RE
      ( \env -> case mx env of
          Return a -> Return a
          Throw e -> runReEx (f e) env
      )

-- Functor and Applicative instances

instance Functor (ReEx env err) where
  fmap = liftM

instance Applicative (ReEx env err) where
  pure = return
  (<*>) = ap
