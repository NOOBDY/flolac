module sorting where

open import Function using (_∘_)
open import Data.Bool using (Bool; true; false; _∧_)
--open import Data.Nat using (ℕ; zero; suc; _+_: )
open import Data.Nat
open import Data.Empty using (⊥)
open import Data.Product using (∃; _×_; _,_; proj₁; proj₂)

data ⊤ : Set where
  tt : ⊤

if_then_else_ : {A : Set} → Bool → A → A → A
if false then x else y = y
if true  then x else y = x

data Vec (A : Set) : ℕ → Set where
  [] : Vec A 0
  _::_ : {n : ℕ} → A → Vec A n → Vec A (suc n)

filterLen : {A : Set} {n : ℕ} → (A → Bool) → Vec A n → ℕ
filterLen f [] = 0
filterLen f (x :: xs) = if f x then suc (filterLen f xs) else filterLen f xs

filter : {A : Set} {n : ℕ} → (f : A → Bool) → (xs : Vec A n) → Vec A (filterLen f xs)
filter f [] = []
filter f (x :: xs) with f x
... | true  = x :: filter f xs
... | false = filter f xs

_++_ : {n m : ℕ} {A : Set} → Vec A n → Vec A m → Vec A (n + m)
[] ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

data Σ (A : Set) (P : A → Set) : Set where
  _,_ : (x : A) → P x → Σ A P

syntax Σ A (λ x → M) = Σ[ x ∶ A ] M
