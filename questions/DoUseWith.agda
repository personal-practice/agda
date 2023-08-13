open import Prelude.Init hiding (mapMaybe); open SetAsType
open L.Mem
open import Prelude.Bifunctor
open import Prelude.Lists.Membership using (Is-here; Is-there)

module _ {A B : Set} (f : A → Maybe B) where

private variable
  x : A; y : B
  xs xs′ : List A; ys : List B

mapMaybe : (A → Maybe B) → List A → List B
mapMaybe p []       = []
mapMaybe p (x ∷ xs) with p x
... | just y  = y ∷ mapMaybe p xs
... | nothing =     mapMaybe p xs

∈-mapMaybe⁺ : x ∈ xs → f x ≡ just y → y ∈ mapMaybe f xs
∈-mapMaybe⁺ {xs = x ∷ _} x∈ eq
  with x∈
... | here refl rewrite eq = here refl
... | there x∈′
  with IH ← ∈-mapMaybe⁺ x∈′ eq
  with f x
... | nothing = IH
... | just _  = there IH

∈-mapMaybe⁻ : y ∈ mapMaybe f xs
            → ∃ λ x → (x ∈ xs) × (f x ≡ just y)
∈-mapMaybe⁻ {y = y} {xs = x ∷ xs} y∈
  with f x | inspect f x
... | nothing | _ = map₂′ (map₁ there) (∈-mapMaybe⁻ y∈)
... | just y′ | PropEq.[ fx≡ ]
  with y∈
... | here refl = x , here refl , fx≡
... | there y∈′ = map₂′ (map₁ there) (∈-mapMaybe⁻ y∈′)

∈-mapMaybe⁻-nothing : (y∈ : y ∈ mapMaybe f (x ∷ xs))
  → f x ≡ nothing
  → Is-there (∈-mapMaybe⁻ y∈ .proj₂ .proj₁)
∈-mapMaybe⁻-nothing {x = x} {xs = xs} y∈ fx≡
  with f x | inspect f x
... | nothing | _ = tt

∈-mapMaybe⁻-here : (y∈ : y ∈ mapMaybe f (x ∷ xs))
  → Is-here $ ∈-mapMaybe⁻ y∈ .proj₂ .proj₁
  → Is-here y∈
∈-mapMaybe⁻-here {x = x} {xs = xs} y∈ y∈≡
  with f x    | inspect f x
... | nothing | _ = case y∈≡ of λ ()
... | just _  | _ with here _ ← y∈ = tt

mapMaybe-⊆ : ∀ {ys} → xs ⊆ ys → mapMaybe f xs ⊆ mapMaybe f ys
mapMaybe-⊆ {xs = x ∷ xs} {ys = ys} xs⊆ fx∈ =
  let x , x∈ , fx≡ = ∈-mapMaybe⁻ fx∈
  in  ∈-mapMaybe⁺ (xs⊆ x∈) fx≡
