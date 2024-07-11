-- by Josh Ko
-- so idak how this work
open import Data.Sum
open import Data.Empty
open import Relation.Nullary

LEM : Set → Set
LEM p = p ⊎ ¬ p

DNE : Set → Set
DNE p = ¬ ¬ p → p

lem→dne : ({A : Set} → LEM A) → ({A : Set} → DNE A)
lem→dne lem {A} ¬¬a with lem {A}
... | inj₁ a  = a
... | inj₂ ¬a = ⊥-elim (¬¬a ¬a)

huh : ((A B : Set) → (¬ B → ¬ A) → (A → B))
   -----------------------
    → ({C : Set} → LEM C)
huh prop {A} = {!!}
