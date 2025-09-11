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
N-refl : ∀ (a : ℕ) → a ≡ a
N-refl a = refl

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

-- These are canonically axioms, but are just provable by definition under Agda's type checker

succNotZero : ∀ (n : ℕ) → ¬ (succ n ≡ zero)
succNotZero zero = λ ()
succNotZero (succ n) = λ ()

succInj : ∀ {n m : ℕ} → (succ n) ≡ (succ m) → n ≡ m
succInj refl = refl

-- We can use induction to prove properties indexed by natural numbers

ℕ-induction :
  ∀ (n : ℕ) (P : ℕ → Set)
  → P zero
  → (s : ∀ (m : ℕ) → P m → P (succ m))
  → P n
ℕ-induction zero _ Pzero _ = Pzero
ℕ-induction (succ n) P Pzero Pn→P-succ-n =
  Pn→P-succ-n n (ℕ-induction n P Pzero Pn→P-succ-n)

-- We can use induction to define sequences.

record recSeq : Set where
  field
    c : ℕ
    aₙs : ℕ → ℕ
    fₙs : ∀ (n : ℕ) → ℕ → ℕ
    baseCase : aₙs zero ≡ c
    recursion : ∀ (n : ℕ) → aₙs (succ n) ≡ fₙs n (aₙs n)

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
                        ; recursion = λ n → refl
                        }

-- Defining addition in the normal way
infix 40 _+_
_+_ : ℕ → ℕ → ℕ
zero   + m = m
succ n + m = succ (n + m)

lemma2-2-2-→ :
  ∀ (n : ℕ)
  → n + zero ≡ n
  → (succ n) + zero ≡ succ n
lemma2-2-2-→ n n+zero≡n rewrite n+zero≡n = refl

lemma2-2-2 : ∀ (n : ℕ) → n + zero ≡ n
lemma2-2-2 n = ℕ-induction n (λ x → x + zero ≡ x) refl lemma2-2-2-→

lemma2-2-3-→ :
  ∀ (m n : ℕ)
  → n + succ m ≡ succ (n + m)
  → succ n + succ m ≡ succ (succ n + m)
lemma2-2-3-→ _ _ eq rewrite eq = refl

lemma2-2-3 : ∀ (n m : ℕ) → n + succ m ≡ succ (n + m)
lemma2-2-3 zero _ = refl
lemma2-2-3 (succ n) m with lemma2-2-3-→ m
... | hyp =
  ℕ-induction
    n
    (λ x → succ x + succ m ≡ succ (succ x + m))
    refl
    (λ n' → hyp (succ n'))

ℕ-+-comm-→ :
  ∀ (m n : ℕ)
  → n + m ≡ m + n
  → (succ n) + m ≡ m + succ n
ℕ-+-comm-→ zero _ eq rewrite eq = refl
ℕ-+-comm-→ m n eq rewrite eq with lemma2-2-3 n m
... | hyp = ℕ-symm (lemma2-2-3 m n)

-- In the process of formalizing commutativity of addition of natural numbers,
-- I have decided to never use implicit variables ever.

ℕ-+-comm : ∀ (n m : ℕ) → n + m ≡ m + n
ℕ-+-comm n m =
  ℕ-induction
    n
    (λ x → x + m ≡ m + x)
    (ℕ-symm (lemma2-2-2 m))
    (ℕ-+-comm-→ m)

ℕ-+-assoc-→ :
  ∀ (c b a : ℕ) →
  (a + b) + c ≡ a + (b + c)
  → ((succ a) + b) + c ≡ (succ a) + (b + c)
ℕ-+-assoc-→ c b zero hyp = refl
ℕ-+-assoc-→ c b (succ a) hyp rewrite hyp = refl

-- Addition over natural numbers is associative

ℕ-+-assoc : ∀ (a b c : ℕ) → (a + b) + c ≡ a + (b + c)
ℕ-+-assoc zero b c = refl
ℕ-+-assoc a b c =
  ℕ-induction
    a
    (λ x →  (x + b) + c ≡ x + (b + c))
    refl
    (ℕ-+-assoc-→ c b)

-- Left-cancellability of addition over natural numbers.
-- This problem drove me to the brink of madness.

ℕ-+-cancelₗ :
  ∀ (c b a : ℕ)
  → a + b ≡ a + c
  → b ≡ c
ℕ-+-cancelₗ c b zero eq = eq
ℕ-+-cancelₗ c b (succ a) eq =
  ℕ-induction
    a
    (λ x → b ≡ c)
    (ℕ-+-cancelₗ c b a (succInj eq))
    λ m x → x

ℕ-+-introₗ :
  ∀ (c b a : ℕ)
  → b ≡ c
  → a + b ≡ a + c
ℕ-+-introₗ c b a refl = refl

data ℕ-pos (a : ℕ) : Set where
  proof : ¬ (a ≡ zero) → ℕ-pos a

prop2-2-8 : ∀ (a b : ℕ) → ℕ-pos a → ℕ-pos (a + b)
prop2-2-8 zero b (proof x) =
  proof λ _ →  x refl
prop2-2-8 (succ a) b (proof p) =
  proof
    λ x → succNotZero
    (a + b) x

-- Agda can directly find this through normalization

corr2-2-9 :
  ∀ (a b : ℕ)
  → a + b ≡ zero
  → (a ≡ zero) × (b ≡ zero)
corr2-2-9 zero zero a+b≡zero = ⟨ a+b≡zero , a+b≡zero ⟩

succ-≡ : ∀ (a : ℕ) ℕ → Set
succ-≡ a = λ b → succ b ≡ a

lemma2-2-10-∃ :
  ∀ (a : ℕ)
  → ℕ-pos a
  → Σ ℕ (succ-≡ a)
lemma2-2-10-∃ zero (proof p) = ⊥-elim (p refl)
lemma2-2-10-∃ (succ n) p = [ n , refl ]

lemma2-2-10-unique :
  ∀ (a b c : ℕ)
  → (succ-≡ a b × succ-≡ a c)
  → b ≡ c
lemma2-2-10-unique _ _ _ ⟨ refl , refl ⟩ = refl

le-sat : ∀ (a b : ℕ) → ℕ → Set
le-sat a b = λ c → a ≡ b + c

data _≤_ (a b : ℕ) : Set where
  le : Σ ℕ (le-sat a b) → a ≤ b

data _<_ (a b : ℕ) : Set where
  lt : (a ≤ b) × (¬ (a ≡ b)) → a < b

data _≥_ (a b : ℕ) : Set where
  ge : b ≤ a → a ≥ b

data _>_ (a b : ℕ) : Set where
  gt : b < a → a > b

≥-refl : (a : ℕ) → a ≥ a
≥-refl a = ge (le [ zero , ℕ-symm (lemma2-2-2 a) ])

-- Murdered by pattern-matching

≥-trans : ∀ (a b c : ℕ) → a ≥ b → b ≥ c → a ≥ c
≥-trans
  a b c
  (ge (le [ b' , refl ]))
  (ge (le [ c' , refl ])) rewrite ℕ-+-assoc a b' c' =
    ge ( le
         [ c' + b'
         , ℕ-+-introₗ
           (c' + b')
           (b' + c')
           a
           (ℕ-+-comm b' c')
         ]
        )
