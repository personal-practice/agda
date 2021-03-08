module RecordModuleImpIrr where

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

Symmetric : ∀ {A : Set} → (A → A → Set) → Set
Symmetric _≈_ = ∀ {x} y → x ≈ y → y ≈ x
-- Symmetric _≈_ = ∀ x y → x ≈ y → y ≈ x

record Signature : Set₁ where
  field
    A : Set
    _≈_ : A → A → Set
    ≈-sym : Symmetric _≈_

module Implementation where
  record A : Set where
    field
      x : Nat
      .pr : x ≡ 0
  open A

  _≈_ : A → A → Set
  a ≈ b = x a ≡ x b
  -- _≈_ = _≡_

  postulate
    ≈-sym : Symmetric _≈_

test : Signature
test = record {Implementation}
