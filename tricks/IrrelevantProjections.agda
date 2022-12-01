{-# OPTIONS --irrelevant-projections #-}
open import Prelude.Init

record Squash {ℓ}(A : Set ℓ) : Set ℓ where
  constructor squash
  field .unsquash : A
open Squash

-- ok:
sqT≡sqF : squash true ≡ squash false
sqT≡sqF = refl

-- this is not provable, issue #543 fixed
.irrT≡F : true ≡ false
irrT≡F = subst (λ s → unsquash (squash true) ≡ unsquash s) sqT≡sqF refl

-- the rest is easy
T≠F : true ≡ false → ⊥
T≠F p = subst T p tt

.irr⊥ : ⊥
irr⊥ = T≠F irrT≡F

rel⊥ : .⊥ → ⊥
rel⊥ ()

absurd : ⊥
absurd = rel⊥ irr⊥
