module NoInstanceInVariable where

open import Data.Unit using (tt)
open import Data.Nat  using (ℕ)
open import Data.Bool using (T)

open import Prelude.DecEq


_ : T (5 == 5)
_ = tt

-- instance
--   DecEqℕ : DecEq ℕ
--   DecEqℕ = DecEq-ℕ

variable
  -- test : ∀ (a b : ℕ) → T (a == b)
  test : ∀ (a b : ℕ) → T (_==_ {{DecEq-ℕ}} a b)
