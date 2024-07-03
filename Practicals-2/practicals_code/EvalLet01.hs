import Prelude ()
import MiniPrelude

data Expr = Num Int | Neg Expr | Add Expr Expr
          | Div Expr Expr
          | Var Name | Let Name Expr Expr
  deriving Show

data Except err a = Return a | Throw err
  deriving Show

data Err = DivByZero | VarNotFound Name
  deriving Show

type Name = String

type Env = [(Name, Int)]
-- What if we define
-- type Env = Name -> Maybe Int

-- The function
--   lookup :: Eq a => a -> [(a, b)] -> Maybe b
-- is defined in GHC.List and imported here.

-- eval :: -- what's its type?
eval = undefined

tstExpr00 :: Expr
tstExpr00 = Let "x" (Num 3)
             (Add (Add (Var "x") (Let "x" (Num 4) (Var "x")))
                  (Neg (Var "x")))
--

data ReEx env err a = RE (env -> Except err a)

type EvalMonad = ReEx Env Err

runReEx :: ReEx env err a -> env -> Except err a
runReEx (RE f) = f

instance Monad (ReEx env err) where
  return = undefined
  (>>=) = undefined

instance MonadReader env (ReEx env err) where
  ask = undefined
  local = undefined

instance MonadExcept err (ReEx env err) where
  throw = undefined
  catchE = undefined

-- Functor and Applicative instances

instance Functor (ReEx env err) where
  fmap = liftM

instance Applicative (ReEx env err) where
  pure  = return
  (<*>) = ap
