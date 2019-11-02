--------------------------------------------------------
-- How to pass termination checking in this case??
--------------------------------------------------------
module DecEqIndexed where

open import Data.Bool    using (Bool; true; false; _∧_)
open import Data.Nat     using (ℕ; _≟_; _≡ᵇ_)
open import Data.Product using (_,_; ∃-syntax)

open import Relation.Nullary                      using (yes; no)
open import Relation.Binary                       using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- Termination checking fails, due to the index being an arbitrary type (i.e. ∈ Set)
module Fails where
  infix 3 _`=_
  data S : Set → Set where
    `_             : ℕ → S ℕ
    _`=_           : S ℕ → S ℕ → S Bool
  ∃S = ∃[ A ] S A

  _≡?_ : ∃S → ∃S → Bool
  (.ℕ , (` x))       ≡? (.ℕ , (` y))         = x ≡ᵇ y
  (.ℕ , (` _))       ≡? (.Bool , (_ `= _))   = false
  (.Bool , (_ `= _)) ≡? (.ℕ , (` _))         = false
  (.Bool , (x `= y)) ≡? (.Bool , (x′ `= y′)) = ((_ , x) ≡? (_ , x′)) ∧ ((_ , y) ≡? (_ , y′))

-- Works if we replace Set with representation of a fixed universe
module Succeeds where
  data Type : Set where
    `Bool `ℕ : Type
    _⇒_ : Type → Type → Type

  infix 3 _`=_
  data S : Type → Set where
    `_             : ℕ → S `ℕ
    _`=_           : S `ℕ → S `ℕ → S `Bool
  ∃S = ∃[ A ] S A

  _≡?_ : ∃S → ∃S → Bool
  (.`ℕ , (` x))       ≡? (.`ℕ , (` y))         = x ≡ᵇ y
  (.`ℕ , (` _))       ≡? (.`Bool , (_ `= _))   = false
  (.`Bool , (_ `= _)) ≡? (.`ℕ , (` _))         = false
  (.`Bool , (x `= y)) ≡? (.`Bool , (x′ `= y′)) = ((_ , x) ≡? (_ , x′)) ∧ ((_ , y) ≡? (_ , y′))
