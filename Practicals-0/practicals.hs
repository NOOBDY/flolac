-- 1.a)
poly :: (Floating a) => a -> a -> a -> a -> a
poly a b c x = a * x ** 2 + b * x + c

-- 1.b)
poly1 x = poly 1 2 1

-- 1.c)
poly2 a b c = poly a b c 2

-- 2.a)
quad :: Int -> Int
quad x = x ^ 4

-- 2.b)
twice :: (a -> a) -> (a -> a)
twice f x = f (f x) -- repeat the same function f :: a -> a twice

-- 2.c)
quad' :: Int -> Int
quad' = twice (^ 2)

-- 3)
twice' :: (a -> a) -> (a -> a)
twice' f = f . f

-- 3.a) yes
-- 3.b) function composition & eta reduction

-- 4.a)
forktimes :: (t -> Int) -> (t -> Int) -> t -> Int
forktimes f g x = f x * g x

-- 4.b)
f = forktimes (+ 1) (+ 2)

-- 4.c)
lift2 :: (a -> a -> a) -> (a -> a) -> (a -> a) -> a -> a
lift2 h f g x = h (f x) (g x)

-- 4.d)
f' = lift2 (*) (+ 1) (+ 2)
