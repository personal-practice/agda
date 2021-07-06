open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.Equality using (_≡_)

module Issue5464 where

record Valid (A : Set) : Set₁ where
  field 𝕍 : A → Set
open Valid ⦃ ... ⦄

variable n : Nat

instance
  I : Valid Nat
  I .𝕍 = _≡ 0

module H₁ .(p : 𝕍 n) where
  RETURN = Nat

[1] : -- ∀ {n}
  -- (p : 𝕍 n) →
  .(p : 𝕍 ⦃ I ⦄ n) →
  -- (p : n ≡ 0) →
  let open H₁ p in
  RETURN
[1] _ = 1

module UlfMinimal where
  open import Agda.Builtin.Bool
  open import Agda.Builtin.Nat

  F : Bool → Set
  F false = Nat
  F true  = Nat

  data It : Bool → Set where
    false : It false
    true  : It true

  postulate
    _:=_ : ∀ b → It b → Set

  module H (n : Nat) where

  works : (let ?b : Bool
               ?b = _)
          (p : F ?b) →
          ?b := false →       -- solves ?b
          (let open H p) →    -- so this is fine
          Nat
  works _ _ = 0

  -- fails : (let ?b : Bool
  --              ?b = _)
  --         (p : F ?b) →
  --         (let open H p) →    -- fails here before ?b is unsolved
  --         ?b := false →
  --         Nat
  -- fails _ _ = 0
