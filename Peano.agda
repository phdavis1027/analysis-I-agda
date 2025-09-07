module Peano where

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; _≢_; cong; trans; sym)
open import Function
  using (_∘_)

open import Logic

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

ℕ-refl : ∀ {a : ℕ} → a ≡ a
ℕ-refl = refl

ℕ-symm : ∀ {a b : ℕ} → a ≡ b → b ≡ a
ℕ-symm refl = refl

ℕ-trans : ∀ {a b c : ℕ} → a ≡ b → b ≡ c → a ≡ c
ℕ-trans refl refl = refl

open EqRel {{...}} public

instance
  ≡-ℕ : EqRel ℕ
  ≡-ℕ =
    record
    { _≃_          = _≡_
    ; reflexivity  = ℕ-refl
    ; symmetry     = ℕ-symm
    ; transitivity = ℕ-trans
   }

succNotZero : ∀ (n : ℕ) → ¬ (succ n ≡ zero)
succNotZero zero = λ ()
succNotZero (succ n) = λ ()

succInj : ∀ {n m : ℕ} → (succ n) ≡ (succ m) → n ≡ m
succInj refl = refl

ℕ-induction :
  ∀ (n : ℕ) (P : ℕ → Set)
  → P zero
  → (s : ∀ {m : ℕ} → P m → P (succ m))
  → P n
ℕ-induction zero _ Pzero _ = Pzero
ℕ-induction (succ n) P Pzero Pn→P-succ-n = Pn→P-succ-n (ℕ-induction n P Pzero Pn→P-succ-n)

record recSeq : Set where
  field
    c : ℕ
    aₙs : ℕ → ℕ
    fₙs : ∀ (n : ℕ) → ℕ → ℕ
    baseCase : aₙs zero ≡ c
    recursion : ∀ {n : ℕ} → aₙs (succ n) ≡ fₙs n (aₙs n)

aₙsImpl :
  ℕ
  → (∀ (n : ℕ) → ℕ → ℕ)
  → ℕ
  → ℕ
aₙsImpl c fₙs zero =  c
aₙsImpl c fₙs (succ n) = fₙs n (aₙsImpl  c fₙs n)

ℕ-recSeq :
  (∀ (n : ℕ) → (ℕ → ℕ))
  → ℕ
  → recSeq
ℕ-recSeq fₙs c = record { c = c
                        ; aₙs = λ n → aₙsImpl c fₙs n
                        ; fₙs =  fₙs
                        ; baseCase = refl
                        ; recursion = refl
                        }
