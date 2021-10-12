open import Agda.Builtin.Unit

module InstanceConstructors (_ : ⊤) where

it : ∀ {A : Set} → ⦃ A ⦄ → A
it ⦃ x ⦄ = x

data X : Set where
  instance x : X

_ : X
_ = it

module M₁ (_ : ⊤) where

  data Y : Set where
    instance x : Y

  _ : Y
  _ = it

module M₂ where

  open M₁ tt

  _ : X
  _ = it

_ : M₁.Y tt
_ = it

open M₁ tt
_ : Y
_ = it
