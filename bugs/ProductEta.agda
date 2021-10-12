module ProductEta where

open import Data.Product
open import Data.List
open import Agda.Builtin.Equality

postulate A B : Set

module _ (xys : List (A × B)) where
  xs = proj₁ (unzip xys)
  module H (_ : xs ≡ []) where
    i = xs

data X : List A → Set where
  [⊤] : ∀ {xys : List (A × B)}
    → let xs = proj₁ (unzip xys) in
      (eq : xs ≡ [])
    → let open H xys eq in
      X i

  [⊥] : ∀ {xys : List (A × B)}
    → let xs , _ = unzip xys in
      (eq : xs ≡ [])
    → let open H xys eq in
      X i
