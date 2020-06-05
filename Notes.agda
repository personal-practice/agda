module Notes where

open import Data.Unit
open import Data.Product hiding (map)
open import Data.Nat
open import Data.List
open import Data.Vec using (Vec)

open import Relation.Binary.PropositionalEquality hiding ([_])

∃Vec : Set
∃Vec = ∃ (Vec ⊤)

indices : List ∃Vec → List ℕ
indices = map proj₁

--

Vec′ : ℕ → Set
Vec′ n = Σ[ xs ∈ List ⊤ ] (length xs ≡ n)

∃Vec′ : Set
∃Vec′ = ∃ Vec′

indices′ : List ∃Vec′ → List ℕ
indices′ = map proj₁

--

inds : ∀ {B : ℕ → Set} → List (Σ ℕ B) → List ℕ
inds = map proj₁

--

ams-filter∘map : ∀ {}
  → AMS $ filter (P? ∘ f) xs
  → AMS $ filter P? (map f xs)

ams-filter∘map′ : ∀ {}
  → AMS $ filter P? (map f xs)
  → AMS $ filter (P? ∘ f) xs

  ∀ {P : A → Set} {P? : Unary.Decidable P} {rv : R → A} {hv : H → A} {r→h : R → H} {xs : List H}
  → (rv≗ : rv ≗ (hv ∘ r→h))
  → AMS $ filter (P? ∘ rv) xs             ≡⟨ ams-filter∘map ⟩
    AMS $ filter P? (map rv xs)           ≡⟨ rewrite | map-cong rv≗ xs ⟩
    AMS $ filter P? (map (hv ∘ r→h) xs)   ≡⟨ rewrite | map-compose {g = hv} {f = r→h} xs ⟩
    AMS $ filter P? (map hv $ map r→h xs) ≡⟨ ams-filter∘map′ ⟩
  → AMS $ filter (P? ∘ hv) (map r→h xs)
am-ap′ = ?
