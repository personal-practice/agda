-- Issue #5833
open import Data.Empty
open import Data.Unit
open import Data.Product
open import Data.Maybe
open import Data.List
open import Data.List.Relation.Unary.Any
open import Data.List.Membership.Propositional
open import Relation.Binary.PropositionalEquality as ≡ using (refl; _≡_; inspect)

variable
  A B : Set
  x : A
  y : B
  xs : List A

Is-there : x ∈ xs → Set
Is-there = λ where
  (here _)  → ⊥
  (there _) → ⊤

module _ (f : A → Maybe B) where
  ∈-mapMaybe⁻ : y ∈ mapMaybe f xs
              → ∃ λ x → (x ∈ xs) × (f x ≡ just y)
  ∈-mapMaybe⁻ {y = y} {xs = x ∷ xs} y∈
  --   with f x | inspect f x
  -- ... | nothing | _ = map₂ (map₁ there) (∈-mapMaybe⁻ y∈)
  -- ... | just y′ | ≡.[ fx≡ ]
    with f x in fx≡
  ... | nothing = map₂ (map₁ there) (∈-mapMaybe⁻ y∈)
  ... | just y′
    with y∈
  ... | here refl = x , here refl , fx≡
  ... | there y∈′ = map₂ (map₁ there) (∈-mapMaybe⁻ y∈′)

  ∈-mapMaybe⁻-nothing : (y∈ : y ∈ mapMaybe f (x ∷ xs))
    → f x ≡ nothing
    → Is-there (∈-mapMaybe⁻ y∈ .proj₂ .proj₁)
  ∈-mapMaybe⁻-nothing {x = x} {xs = xs} y∈ fx≡
  --   with f x | inspect f x
  -- ... | nothing | _ = tt
  --   with f x in _
  -- ... | nothing | _ = tt
    with ∈-mapMaybe⁻ y∈
  ... | _ , here refl , fx≢ rewrite fx≡ with () ← fx≢
  ... | _ , there _   , _ = _
