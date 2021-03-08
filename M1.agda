open import Prelude.Init
open import Prelude.DecEq
open import Prelude.Decidable

module M1 (A : Set) {{_ : DecEq A}} where

variable
  x y : A

_~_ : Rel₀ A
_~_ = _≡_

instance
  Dec-~ : (x ~ y) ⁇
  Dec-~ .dec = _ ≟ _
