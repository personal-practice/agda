--------------------------------------------------------
-- How to pass termination checking in this case??
--------------------------------------------------------
module DecEqIndexed where

open import Data.Bool    using (Bool)
open import Data.Nat     using (ℕ; _≟_)
open import Data.Product using (_×_; _,_; ∃-syntax; Σ-syntax)

open import Relation.Nullary                      using (yes; no)
open import Relation.Binary                       using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

data S : Set → Set where
  `_             : ℕ → S ℕ
  _`=_           : S ℕ → S ℕ → S Bool

infix 3 _`=_

_ : S Bool
_ = ` 0 `= ` 1

_≟∃ₛ_ : Decidable {A = ∃[ A ] S A} _≡_
_≟ₛ_ : ∀ {A} → Decidable {A = S A} _≡_

-- Termination checking fails
(.ℕ , (` x)) ≟∃ₛ (.ℕ , (` x₁))
  with x ≟ x₁
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl = yes refl
(.ℕ , (` x)) ≟∃ₛ (.Bool , (snd₁ `= snd₂)) = no (λ ())

(.Bool , (snd `= snd₂)) ≟∃ₛ (.ℕ , (` x)) = no (λ ())
(.Bool , (x `= y)) ≟∃ₛ (.Bool , (x′ `= y′))
  with x ≟ₛ x′ | y ≟ₛ y′
... | no ¬p     | _        = no λ{ refl → ¬p refl }
... | _         | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl  | yes refl = yes refl

_≟ₛ_ {A} x y with (A , x) ≟∃ₛ (A , y)
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl = yes refl
-- fails with "I'm not sure if there should be a case...'
-- (` x) ≟ₛ y = {!y!}
-- (x `= x₁) ≟ₛ y = {!y!}
