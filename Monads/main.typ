== Monad Rules

```hs
m :: * -> *
return :: a -> ma
(>>=) :: ma -> (a -> mb) -> mb
```
---
```hs
1. mx >>= return = mx
2. return x >>= k = kx
3. (mx >>= k0) >>= k1 = mx >>= (\x -> k0 x >>= k1)
```
