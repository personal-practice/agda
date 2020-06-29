open import Prelude.DecEq

module Expansion1 (A : Set) {{_ : DecEq A}} where

open import Expansion0 A

f : Ty → Set
f t = {!!}
-- ** Wrong expansion
-- f (Expansion0.Ty.unit x) = ?
-- f (Expansion0.Ty.pair x x₁) = ?
