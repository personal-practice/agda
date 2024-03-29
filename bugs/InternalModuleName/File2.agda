------------------------------------------------------------------------
-- Singleton predicate for various kinds of lists.

module Prelude.Lists.Singletons where

open import Prelude.Init
-- open Nat using (_≤_; _≤?_; _≥_)
-- open L.Mem using (_∈_)
-- open import Prelude.ToList
-- open import Prelude.Bifunctor
open import Prelude.Lists.Combinatorics
open import Prelude.Lists.Empty

private variable
  A : Set ℓ
  B : Set ℓ′
  x : A
  xs : List A
  xss : List (List A)

Singleton : List A → Set
Singleton []       = ⊥
Singleton (_ ∷ []) = ⊤
Singleton (_ ∷ _)  = ⊥

construct-Singleton : ∃[ x ] (xs ≡ x ∷ []) → Singleton xs
construct-Singleton (_ , refl) = tt

destruct-Singleton : Singleton xs → ∃ λ x → xs ≡ [ x ]
destruct-Singleton {xs = []}          ()
destruct-Singleton {xs = _ ∷ []}      tt = _ , refl
destruct-Singleton {xs = _ ∷ (_ ∷ _)} ()

Singleton⇒len≡ : Singleton xs → length xs ≡ 1
Singleton⇒len≡ s-xs rewrite proj₂ $ destruct-Singleton s-xs = refl

len≡⇒Singleton : length xs ≡ 1 → Singleton xs
len≡⇒Singleton {xs = []}        ()
len≡⇒Singleton {xs = _ ∷ []}    refl = tt
len≡⇒Singleton {xs = _ ∷ _ ∷ _} ()

singleton-map : ∀ {f : A → B}
  → Singleton xs
  → Singleton (map f xs)
singleton-map {xs = []}        ()
singleton-map {xs = _ ∷ []}    tt = tt
singleton-map {xs = _ ∷ _ ∷ _} ()

singleton-subseqs : Singleton xs → subsequences xs ≡ [] ∷ xs ∷ []
singleton-subseqs {xs = []}        ()
singleton-subseqs {xs = _ ∷ []}    tt = refl
singleton-subseqs {xs = _ ∷ _ ∷ _} ()

singleton-mapWith∈  : ∀ {x : A} {xs : List A} {x′ : B} {f : ∀ {x} → x ∈ xs → B}
  → (∀ x∈ → f {x} x∈ ≡ x′)
  → xs ≡ [ x ]
  → mapWith∈ xs f ≡ [ x′ ]
singleton-mapWith∈ f≡ refl rewrite f≡ (here refl) = refl

singleton∈ :
    (s-xs : Singleton xs)
  → proj₁ (destruct-Singleton s-xs) ∈ xs
singleton∈ s-xs with _ , refl ← destruct-Singleton s-xs = here refl

singleton-concat : ∀ {x : A} {xss : List (List A)}
  → xss ≡ [ [ x ] ]
  → Singleton (concat xss)
singleton-concat refl = tt

All-singleton : {x : A} {xs : List A} {P : A → Set}
 → xs ≡ [ x ]
 → All P xs
 → P x
All-singleton refl (Px ∷ []) = Px

---

AtMostSingleton : Pred₀ (List A)
AtMostSingleton []          = ⊤
AtMostSingleton (_ ∷ [])    = ⊤
AtMostSingleton (_ ∷ _ ∷ _) = ⊥

ams-single : ∀ {x : A} {xs : List A}
  → AtMostSingleton (x ∷ xs)
  → xs ≡ []
ams-single {xs = []}    _ = refl
ams-single {xs = _ ∷ _} ()

ams-∈ : ∀ {x : A} {xs : List A}
  → AtMostSingleton xs
  → x ∈ xs
  → xs ≡ [ x ]
ams-∈ {xs = []}        _  ()
ams-∈ {xs = x ∷ []}    _  (here refl) = refl
ams-∈ {xs = _ ∷ _ ∷ _} () _

ams-filter⁺ : ∀ {xs : List A} {P : A → Set} {P? : Decidable¹ P}
  → AtMostSingleton xs
  → AtMostSingleton (filter P? xs)
ams-filter⁺ {xs = []}                  tt = tt
ams-filter⁺ {xs = x ∷ []}    {P? = P?} tt with P? x
... | yes _ = tt
... | no  _ = tt
ams-filter⁺ {xs = _ ∷ _ ∷ _}           ()

postulate
  ams-filter-map : ∀ {xs : List A} {f : A → B} {P : Pred₀ B} {P? : Decidable¹ P}
    → AtMostSingleton $ filter P? (map f xs)
    → AtMostSingleton $ filter (P? ∘ f) xs

  ams-filter-reject : ∀ {x : A} {xs : List A} {P : Pred₀ A}
    → (P? : Decidable¹ P)
    → ¬ P x
    → AtMostSingleton $ filter P? xs
    → AtMostSingleton $ filter P? (x ∷ xs)

  ams-filter-accept : ∀ {x : A} {xs : List A} {P : Pred₀ A}
    → (P? : Decidable¹ P)
    → P x
    → Null $ filter P? xs
    → AtMostSingleton $ filter P? (x ∷ xs)

  length≤1⇒ams : ∀ {xs : List A}
    → length xs ≤ 1
    → AtMostSingleton xs

  ams-count : ∀ {P : Pred₀ A} {P? : Decidable¹ P} {xs : List A} {f : A → Maybe B}
    → (∀ x → P x → Is-just (f x))
    → count P? xs ≤ 1
    → AtMostSingleton (mapMaybe f xs)

am-¬null⇒singleton : ∀ {xs : List A}
  → AtMostSingleton xs
  → ¬Null xs
  → Singleton xs
am-¬null⇒singleton {xs = []         } tt ¬p = ⊥-elim (¬p refl)
am-¬null⇒singleton {xs = (_ ∷ [])   } _  _  = tt
am-¬null⇒singleton {xs = (_ ∷ _ ∷ _)} ()

---

Singleton⁺ : List⁺ A → Set
Singleton⁺ (_ ∷ []) = ⊤
Singleton⁺ (_ ∷ _)  = ⊥

destruct-Singleton⁺ : ∀ {xs : List⁺ A}
  → Singleton⁺ xs
  → ∃ λ x → xs ≡ [ x ]⁺
destruct-Singleton⁺ {xs = _ ∷ []}      tt = _ , refl
destruct-Singleton⁺ {xs = _ ∷ (_ ∷ _)} ()

singleton⁺ : ∀ {xs : List A}
  → AtMostSingleton xs
  → (xs≢[] : ¬Null xs)
  → Singleton⁺ (toList⁺ xs xs≢[])
singleton⁺ {xs = []}        tt xs≢[] = ⊥-elim $ xs≢[] refl
singleton⁺ {xs = _ ∷ []}    tt xs≢[] = tt
singleton⁺ {xs = _ ∷ _ ∷ _} ()

singleton-concatMap  : ∀ {h : List⁺ A} {f : A → List B}
  → Singleton⁺ h
  → (∀ x → Singleton (f x))
  → Singleton $ concatMap f (toList h)
singleton-concatMap {f = f} h⁺ s-f
  with h , refl ← destruct-Singleton⁺ h⁺
  rewrite ++-identityʳ (f h)
    = s-f h

singleton⇒singleton⁺ : ∀ {xs≢[] : ¬ Null xs}
  → Singleton xs
  → Singleton⁺ (toList⁺ xs xs≢[])
singleton⇒singleton⁺ p rewrite proj₂ $ destruct-Singleton p = tt

postulate
  singleton⁺-map⁺ : ∀ {xs : List⁺ A} {f : A → B} → Singleton⁺ xs → Singleton⁺ (L.NE.map f xs)

---

Singleton² : Pred (List (List A)) _
Singleton² xss = Singleton xss × All Singleton xss

construct-Singleton² :
    xss ≡ [ [ x ] ]
  → Singleton² xss
construct-Singleton² refl = tt , tt ∷ []

destruct-Singleton² : Singleton² xss → ∃ λ x → xss ≡ [ [ x ] ]
destruct-Singleton² (tt , s-xs ∷ [])
  with x , refl ← destruct-Singleton s-xs
     = x , refl

singleton-concat⁺ : Singleton² xss → Singleton (concat xss)
singleton-concat⁺ {xss = []}                  (()   , _)
singleton-concat⁺ {xss = []          ∷ []}    (_    , () ∷ _)
singleton-concat⁺ {xss = (_ ∷ [])    ∷ []}    (_    , _)      = tt
singleton-concat⁺ {xss = (_ ∷ _ ∷ _) ∷ []}    (_    , () ∷ _)
singleton-concat⁺ {xss = _           ∷ _ ∷ _} (()   , _)
