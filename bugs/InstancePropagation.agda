open import Prelude.Init
open import Prelude.DecEq

module InstancePropagation (A : Set) {{_ : DecEq A}} where

postulate
  B : Set
variable
  n : B
postulate
  P : B → Set
  p₁ : P n
