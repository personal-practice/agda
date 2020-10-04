module NoInstanceInVariable where

open import Data.Unit using (tt)
open import Data.Nat  using (ℕ; _≡ᵇ_)
open import Data.Bool using (T; Bool)

record Eq (A : Set) : Set where
  field
    _==_ : A → A → Bool

open Eq {{...}} public

instance
  Eq-ℕ : Eq ℕ
  Eq-ℕ ._==_ = _≡ᵇ_

_ : T (5 == 5)
_ = tt

variable
  -- test : ∀ (a b : ℕ) → T (a == b)
  test : ∀ (a b : ℕ) → T (_==_ {{Eq-ℕ}} a b)

-- see agda issues 3358, 3464, 3523
