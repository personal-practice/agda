open import Prelude.Init hiding (mapMaybe); open SetAsType
open L.Mem
open import Prelude.Bifunctor

module DoNotUseWith {A B : Set} (f : A → Maybe B) where

private variable
  x : A
  y : B
  xs : List A

Is-here Is-there : x ∈ xs → Set
Is-here = λ where
  (here _)  → ⊤
  (there _) → ⊥
Is-there = λ where
  (here _)  → ⊥
  (there _) → ⊤

mapMaybe : (A → Maybe B) → List A → List B
mapMaybe p []       = []
mapMaybe p (x ∷ xs) = case p x of λ where
  (just y) → y ∷ mapMaybe p xs
  nothing  → mapMaybe p xs

∈-mapMaybe⁺ : x ∈ xs → f x ≡ just y → y ∈ mapMaybe f xs
∈-mapMaybe⁺ {xs = x ∷ _} x∈ eq
  with x∈
... | here refl rewrite eq = here refl
... | there x∈′
  with IH ← ∈-mapMaybe⁺ x∈′ eq
  with f x
... | nothing = IH
... | just y  = there IH

∈-mapMaybe⁻ : y ∈ mapMaybe f xs
            → ∃ λ x → (x ∈ xs) × (f x ≡ just y)
∈-mapMaybe⁻ {y = y} {xs = x ∷ xs} y∈
  with f x | inspect f x
... | nothing | _ = map₂′ (map₁′ there) (∈-mapMaybe⁻ y∈)
... | just y′ | PropEq.[ fx≡ ]
  with y∈
... | here refl = x , here refl , fx≡
... | there y∈′ = map₂′ (map₁′ there) (∈-mapMaybe⁻ y∈′)

∈-mapMaybe⁻-nothing : (y∈ : y ∈ mapMaybe f (x ∷ xs))
  → f x ≡ nothing
  → Is-there (∈-mapMaybe⁻ y∈ .proj₂ .proj₁)
∈-mapMaybe⁻-nothing {x = x} {xs = xs} y∈ fx≡
  with f x | inspect f x
... | nothing | _ = tt
