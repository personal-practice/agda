module Sorting where

open import Prelude.Init
open import Prelude.Decidable

private
  variable
    n : ℕ
    mn : Maybe ℕ

_<ᵐ_ : ℕ → Maybe ℕ → Set
_ <ᵐ nothing = ⊤
n <ᵐ just n′ = n < n′

instance
  Dec-<ᵐ : (n <ᵐ mn) ⁇
  Dec-<ᵐ {n}{nothing} .dec = yes tt
  Dec-<ᵐ {n}{just n′} .dec = n <? n′

data Sorted : Pred₀ (List ℕ) where
  [] : Sorted []
  _∷_⊣_ : ∀ x {xs} → Sorted xs → x <ᵐ L.head xs → Sorted (x ∷ xs)

sorted? : Decidable¹ Sorted
sorted? [] = yes []
sorted? (x ∷ xs)
  with ¿ x <ᵐ L.head xs ¿
... | no  x≮ = no $ λ{ (_ ∷ _ ⊣ x<) → x≮ x< }
... | yes x<
  with sorted? xs
... | no ¬p = no $ λ{ (_ ∷ p ⊣ _) → ¬p p }
... | yes p = yes $ x ∷ p ⊣ x<

instance
  DecSorted : Sorted ⁇¹
  DecSorted .dec = sorted? _
