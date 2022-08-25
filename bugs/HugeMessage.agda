open import Prelude.Init
open L.Mem
open import Prelude.Lists.Empty

variable A B : Set

LastAny : ∀ {xs : List A} {P : Pred₀ A} → Pred₀ (Any P xs)
LastAny {xs = xs} = λ where
  (here _)  → Null xs
  (there p) → LastAny p

LastAny-map⁺ : ∀ {xs : List A} (f : A → B) {P : Pred₀ B} (x∈ : Any (P ∘ f) xs)
  → LastAny x∈
  → LastAny (L.Any.map⁺ {f = f} {P = P} x∈)
LastAny-map⁺ = LastAny-map⁺ {!!} {!!}
-- LastAny-map⁺ {!cong f!} {!!}

-- Last∈ : Pred₀ (x ∈ xs)
-- Last∈ = LastAny

-- Last∈-map⁺ : ∀ (f : A → B) (x∈ : x ∈ xs) →
--   Last∈ x∈
--   → Last∈ (L.Mem.∈-map⁺ f x∈)
-- Last∈-map⁺ = LastAny-map⁺ {!cong f!} {!!}
