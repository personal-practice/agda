module InferExistentials where

{- **formal-bitml**
-- = ∃ (∃ (∃ (coher Rˢ Rᶜ)))
-- [BUG] not inferring type of existentials, although dependency is evident
-}

open import Prelude.Init
open import Prelude.Lists

postulate
  A B : Set
  R : A → B → A → B → Set

_~_ : A → B → Set
-- a ~ b = ∃ λ x → ∃ λ y → R a b x y
a ~ b = Product.∃₂ (R a b)

-- postulate
  -- R : (xs : List ℕ) (ys : List ℕ) → xs ↦ String → Set
  -- R : (xs : List ℕ) (ys : List ℕ) → (xs ↦ String) × (ys ↦ ℤ) → Set
  -- R : (xs : List ℕ) (ys : List ℕ) → xs ↦ String → ys ↦ ℤ → Set


-- _~_ : List ℕ → List ℕ → Set
-- a ~ b = ∃ (R a b)
