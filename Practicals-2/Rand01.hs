{-# LANGUAGE AllowAmbiguousTypes #-}
import Prelude ()
import MiniPrelude

 --- X_{n+1} = (a * X_n + c) `mod` m
 ---   m -- the modulus
 ---   a -- the multiplier
 ---   c -- the increment

type Config = (Integer, Integer, Integer)

random :: (MonadState Integer m,
           MonadReader Config m) => m Integer
random = undefined

-- e.g.
-- > runStRe (randoms 10) (9,4,1) 99
-- ([1,5,3,4,8,6,7,2,0,1],1)

randoms :: (MonadState Integer m,
            MonadReader Config m) =>
           Int -> m (List Integer)
randoms = undefined

---

type RandMonad = StRe Config Integer

data StRe e s a = SR (e -> s -> (a, s))

runStRe :: StRe e s a -> e -> s -> (a, s)
runStRe (SR f) = f

instance Monad (StRe e s) where
  return = undefined
  SR mx >>= k = undefined

instance MonadState s (StRe e s) where
  get    = undefined
  put s' = undefined

instance MonadReader e (StRe e s) where
  ask        = undefined
  local f mx = undefined

-- Functor and Applicative instances

instance Functor (StRe e s) where
  fmap = liftM

instance Applicative (StRe e s) where
  pure  = return
  (<*>) = ap
