import Prelude ()
import MiniPrelude

type Graph a = a -> List a
type Path  a = List a

type Set a = List a

g :: Graph Char
g 'a' = "bcd"
g 'b' = "ac"
g 'c' = "bef"
g 'd' = "bea"
g 'e' = "eb"
g 'f' = "f"

--

path :: (Eq a, MonadNondet m, MonadState (Set a) m)
     => Graph a -> a -> m (Path a)
path g x = undefined

visited :: (Eq a, MonadState (Set a) m)
        => a -> m Bool
visited = undefined

choose :: MonadNondet m => List a -> m a
choose = undefined

locate :: (Eq a, MonadNondet m) => a -> List a -> m (List a)
locate = undefined

find :: (Eq a, MonadNondet m, MonadState (Set a) m)
     => Graph a -> a -> a -> m (Path a)
find = undefined

--

data StNd s a = SN (s -> [(a, s)])

type GMonad = StNd (Set Char)

runStNd :: StNd s a -> s -> [(a, s)]
runStNd (SN f) = f

instance Monad (StNd s) where
  return x = undefined
  SN mx >>= k = undefined

instance MonadFail (StNd s) where
  fail = SN undefined

instance MonadAlt (StNd s) where
  SN mx <|> SN my = SN undefined

instance MonadNondet (StNd s) where

instance MonadState s (StNd s) where
  get    = SN undefined
  put s' = SN undefined

-- Functor and Applicative instances

instance Functor (StNd s) where
  fmap = liftM

instance Applicative (StNd s) where
  pure  = return
  (<*>) = ap
