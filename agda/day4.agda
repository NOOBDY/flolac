module day4 where

data ⊥ : Set where

data _∧_ (a b : Set) : Set where
 ⟨_,_⟩ : a → b → a ∧ b

outl : {a b : Set} → a ∧ b → a
outl ⟨ x , y ⟩ = x
outr : {a b : Set} → a ∧ b → b
outr ⟨ x , y ⟩ = y

data _∨_ (a b : Set) : Set where
  inl : a → a ∨ b
  inr : b → a ∨ b

¬_ : Set → Set
¬_ p = p → ⊥

proof : {A : Set} → A → ¬ ¬ A
proof = λ x y → y x

preef : {A : Set} → ¬ (A ∧ (¬ A))
preef = λ x → outr x (outl x)

pruuf : {A : Set} → ¬ ¬ (A ∨ (¬ A))
pruuf = λ x → x (inr λ y → x (inl y))
