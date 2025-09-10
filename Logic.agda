module Logic where

data ⊥ : Set where

data ⊤ : Set where
  tt : ⊤

¬_ : Set → Set
¬ A = A → ⊥

record EqRel (A : Set) : Set₁ where
  field
    _≃_ : A → A → Set
    reflexivity  : ∀ {a : A}     → a ≃ a
    symmetry     : ∀ {a b : A}   → a ≃ b → b ≃ a
    transitivity : ∀ {a b c : A} → a ≃ b → b ≃ c → a ≃ c

negImpl : ∀ {p m : Set} → (p → m) → (¬ m → ¬ p)
negImpl p→m ¬m p = ¬m (p→m p)

record _×_ (A B : Set) : Set where
  constructor ⟨_,_⟩
  field
    l : A
    r : B
