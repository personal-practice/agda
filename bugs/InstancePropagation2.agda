open import Prelude.Init
open import Prelude.DecEq

module InstancePropagation2 (A : Set) {{_ : DecEq A}} where

open import InstancePropagation A -- {{it}}

postulate p₂ : P n
