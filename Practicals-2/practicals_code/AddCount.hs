import Prelude ()
import MiniPrelude

data Expr = Num Int | Add Expr Expr | Mul Expr Expr
  deriving Show

-- count the number of "Add" performed

eval :: MonadState Int m => Expr -> m Int
eval = undefined

-- > runState (eval tstExpr00) 0
-- (6240,2)

tstExpr00, tstExpr01 :: Expr
tstExpr00 = (Num 64 `Add` Num 32) `Mult`
                (Num 1 `Add` Num 64)
tstExpr01 = (Num 32 `Mul` Num 0) `Add` Num 32

---

data State s a = ST (s -> (a, s))

runState :: State s a -> s -> (a, s)
runState (ST f) = f

instance Monad (State s) where
  return x = undefined
  ST mx >>= k = undefined

instance MonadState s (State s) where
  get    = ST undefined
  put s' = ST undefined


-- Functor and Applicative instances

instance Functor (State s) where
  fmap = liftM

instance Applicative (State s) where
  pure  = return
  (<*>) = ap
