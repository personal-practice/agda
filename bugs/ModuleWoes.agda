module ModuleWoes where

open import Data.Nat
open import Data.List
open import Relation.Binary.PropositionalEquality

postulate
  X Y : Set

record _has_ (A : Set) (X : Set) : Set where
  field
    collect : A → List X
open _has_ ⦃ ... ⦄

f : ∀ {A : Set} ⦃ _ : A has ℕ ⦄ → A → List ℕ
f = collect

postulate
  fx : X → List ℕ
  fy : Y → List ℕ

instance
  HX : X has ℕ
  HX .collect = fx

  HY : Y has ℕ
  HY .collect = fy

_≡⟨on:_⟩_ : X → (∀ {A : Set} ⦃ _ : A has ℕ ⦄ → A → List ℕ) → Y → Set
x ≡⟨on: f ⟩ y = f x ≡ f y

module M₁ (x : X) (y : Y) (p : x ≡⟨on: f ⟩ y) where
  p′ : x ≡⟨on: f ⟩ y
  p′ = p


data TEST : (x : X) → (y : Y) → (x ≡⟨on: f ⟩ y) → Set where
  [1] : ∀ {x y}

    → (p : x ≡⟨on: f ⟩ y)
    → let
        open M₁ x y p

        pp : f x ≡ f y
        pp = p′
      in
    --————————————————————————————————————————
      TEST x y pp
