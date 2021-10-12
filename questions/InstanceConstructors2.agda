open import Agda.Builtin.Unit

module InstanceConstructors2 where

open import InstanceConstructors tt

open M₁ tt

_ : Y
_ = it

_ : M₁.Y tt
_ = it

_ : X
_ = it
