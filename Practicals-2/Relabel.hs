import Prelude ()
import MiniPrelude

data Tree a = Tip a | Bin (Tree a) (Tree a)
  deriving Show

relabel :: MonadState Int m => Tree a -> m (Tree Int)
relabel (Tip x) = Tip <$> fresh
relabel (Bin t u) =
  Bin <$> relabel t <*> relabel u

dlabel :: (MonadFail m, Eq a) => Tree a -> m (List a)
dlabel (Tip x) = return [x]
dlabel (Bin t u) =
   cat <$> (assert disjoint (pair <$> dlabel t <*> dlabel u))

---

disjoint :: Eq a => ([a],[a]) -> Bool
disjoint = undefined

---

pair x y = (x, y)
cat (xs,ys) = xs ++ ys

data STE s a = STE (s -> Maybe (a, s))

instance Monad (STE s) where
  -- return x = STE (\s -> Just (x, s))
  return = pure
  STE mx >>= f =
    STE (\s -> case mx s of
           Nothing -> Nothing
           Just (x,s') -> case f x of
                            STE k -> k s')

instance MonadFail (STE s) where
 fail = STE (\s -> Nothing)

instance MonadState s (STE s) where
  get = undefined
  put = undefined

assert :: MonadFail m => (a -> Bool) -> m a -> m a
assert p mx = do x <- mx
                 if p x then return x else fail

fresh :: MonadState Int m => m Int
fresh = do s <- get
           put (s+1)
           return s


-- Functor and Applicative instances

instance Functor (STE s) where
  fmap = liftM

instance Applicative (STE s) where
  pure x = STE (\s -> Just (x, s))
  (<*>) = ap
