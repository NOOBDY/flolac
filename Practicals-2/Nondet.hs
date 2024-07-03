{-# LANGUAGE TypeSynonymInstances, FlexibleContexts, FlexibleInstances #-}
import Prelude ()
import MiniPrelude

-- > runList (choose "abcd")
-- "abcd"

choose :: MonadNondet m => List a -> m a
choose = undefined

-- > runList (prefix "abcd")
-- ["","a","ab","abc","abcd"]

prefix :: MonadNondet m => List a -> m (List a)
prefix = undefined

--

runList :: List a -> List a
runList = id

{-
return and (>>=) for lists are pre-defined. But can you
imagine how they are defined?

instance Monad [] where
  return = ?
  (>>=)  = ?
-}

instance MonadFail [] where
  fail = []

instance MonadAlt [] where
  (<|>) = (++)

instance MonadNondet [] where
