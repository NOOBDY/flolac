module day5 where

open import Data.Nat
open import Data.Bool

data Nat : Set where
  zero : Nat
  suc : Nat → Nat

Cₙ = {X : Set} → (X → X) → X → X

z : Cₙ
z = λ f x → x

s : Cₙ → Cₙ
s = λ n f x → f (n f x)

add : Cₙ → Cₙ → Cₙ
add = λ n m f x → n f (m f x)

data _≡_ {A : Set} : A → A → Set where
  refl : ∀ {x : A} → x ≡ x

{-
sym : ∀ {A : Set} → {x y : A} → (x ≡ y) → (y ≡ x)
sym refl = refl

trans : ∀ {A} → {x y z : A} → (x ≡ y) → (y ≡ z) → (x ≡ z)
trans refl refl = refl
-}

_+++_ : Nat → Nat → Nat
zero +++ n = n
(suc m) +++ n = suc (m +++ n)

{-
thm0 : ((suc zero) +++ (suc zero)) ≡ (suc (suc zero))
thm0 = refl
-}

thm : ∀ {X : Set} {f : X → X} {x} → (add (s z) (s z)) f x ≡ (s (s z)) f x
thm = refl

tonat : Cₙ → Nat
tonat n = n suc zero

thm2 : ∀ {n m : Cₙ} → tonat (add n m) ≡ (tonat n +++ tonat m)
thm2 = ?

thm3 : tonat (s (s z)) ≡ suc (suc zero)
thm3 = refl
