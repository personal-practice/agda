module DependentGeneralizedVariables where

open import Prelude.Init hiding (module M)
open import Prelude.Closures
open import Prelude.Traces

postulate
  X : Set
  _+1 : Op₁ X
  _=0 : Pred₀ X

variable x : X

infix -1 _—→_
data _—→_ : Rel₀ X where
  [suc] : x —→ x +1

instance
  I : HasInitial X
  I .Initial = _=0

open ReflexiveTransitiveClosure _—→_

Run = Trace _—→_

postulate
  _≺_ : Rel₀ Run
  P : Pred₀ Run

Fun : Run → Set
Fun R = (∀ R′ → R′ ≺ R → P R′) → P R

record ℝ (R : Run) : Set where
  field
    f : Fun R

variable
  R : Run
  𝕣 : ℝ R

module M (𝕣 : ℝ R) where
  RET = 𝕣

data Y : (R : Run) → ℝ R → Set where
  [1] : Y R 𝕣
    --   n ≡ 5
    -- → toℕ fn ≡ 5
    --   --————————————————————————————
    -- → T (n , fn)
