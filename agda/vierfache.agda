module vierfache where

open import Data.Nat
open import Data.Bool
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Negation.Core using (¬_; contradiction)

isEven : ℕ → Bool
isEven zero = true
isEven (suc zero) = false
isEven (2+ n) = isEven n

isVierfach : ℕ → Bool
isVierfach zero = true
isVierfach (suc zero) = false
isVierfach (2+ zero) = false
isVierfach (2+ (suc zero)) = false
isVierfach (2+ (2+ n)) = isVierfach n

isVierfach_implies_isEven : ∀ {n : ℕ} → isVierfach n ≡ true → isEven n ≡ true
isVierfach_implies_isEven {zero} prf = refl
isVierfach_implies_isEven {2+ (2+ n)} prf = isVierfach_implies_isEven {n} prf

isNotEven_implies_isNotVierfach : ∀ {n : ℕ} → isEven n ≡ false → isVierfach n ≡ false
isNotEven_implies_isNotVierfach {suc zero} prf = refl
isNotEven_implies_isNotVierfach {2+ (suc zero)} prf = refl
isNotEven_implies_isNotVierfach {2+ (2+ n)} prf = isNotEven_implies_isNotVierfach {n} prf
