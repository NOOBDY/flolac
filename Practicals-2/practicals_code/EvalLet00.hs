import Prelude ()
import MiniPrelude hiding (MonadReader(..))

data Expr = Num Int | Neg Expr | Add Expr Expr
          | Var Name | Let Name Expr Expr

type Name = String

type Env = [(Name, Int)]

-- What if we define
-- type Env = Name -> Maybe Int   --?

-- The function
--   lookup :: Eq a => a -> [(a, b)] -> Maybe b
-- is defined in GHC.List and imported here.



eval :: Expr -> Reader Env Int
eval (Num n) = return n
eval (Neg e) = negate <$> eval e
eval (Add e0 e1) = (+) <$> eval e0 <*> eval e1
eval (Var x) = ask >>= \ env ->
               case lookup x env of
                 Just v -> return v
eval (Let x e0 e1) = eval e0 >>= \v0 ->
                     local ((x,v0):) (eval e1)

tstExpr00 :: Expr
tstExpr00 = Let "x" (Num 3)
             (Add (Add (Var "x") (Let "x" (Num 4) (Var "x")))
                  (Neg (Var "x")))
--

data Reader e a = Rdr (e -> a)

runReader :: Reader e a -> e -> a
runReader (Rdr f) = f

instance Monad (Reader e) where
  return x     = Rdr (\ env -> x)
  Rdr mx >>= f = Rdr (\ env -> runReader (f (mx env)) env)

ask :: Reader e e
ask = Rdr (\ env -> env)

local :: (e -> e) -> Reader e a -> Reader e a
local f mx = Rdr (\env -> runReader mx (f env))

-- Functor and Applicative instances

instance Functor (Reader e) where
  fmap = liftM

instance Applicative (Reader e) where
  pure  = return
  (<*>) = ap
