open import Prelude.Init
  hiding (List; []; _∷_; _++_; Any)
open SetAsType
open import Prelude.InferenceRules

{-
*LEVEL 0*

∙ Definition of lists: [] | x : xs
∙ Operations on lists: _++_ ⋯
∙ Relations on lists: _∈_ ⋯
-}

data List (A : Type) : Type where
  [] : List A
  _∷_ : A → List A → List A

private variable
  A : Type
  x x′ y y′ : A
  xs xs′ ys ys′ : List A

_++_ : Op₂ (List A)
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

data Any (P : Pred₀ A) : Pred₀ (List A) where
  here :

    P x
    ──────────────
    Any P (x ∷ xs)

  there :

    Any P xs
    ──────────────
    Any P (x ∷ xs)

_∈_ : A → List A → Type
_∈_ x = Any (_≡ x)

infixr 6 _++_
infixr 5 _∷_
infix  4 _∈_

-- *LEVEL 1* Properties of level-0 interactions.

open import Prelude.Bifunctor
∈-++⁻ :
  x ∈ xs ++ ys
  ───────────────
  x ∈ xs ⊎ x ∈ ys
∈-++⁻ {xs = []}    = inj₂
∈-++⁻ {xs = _ ∷ _} = λ where
  (here px)  → inj₁ $ here px
  (there x∈) → there <$>₁ ∈-++⁻ x∈

∈-++⁺ˡ :
  x ∈ xs
  ───────────────
  x ∈ xs ++ ys
∈-++⁺ˡ {xs = _ ∷ _} = λ where
  (here px)  → here px
  (there x∈) → there $ ∈-++⁺ˡ x∈

∈-++⁺ʳ :
  x ∈ ys
  ───────────────
  x ∈ xs ++ ys
∈-++⁺ʳ {xs = []}    = id
∈-++⁺ʳ {xs = _ ∷ _} = there ∘′ ∈-++⁺ʳ

-- *LEVEL 2* Properties of level-1 interactions.

∈-++⁻∘∈-++⁺ˡ : ∀ {x : A} (x∈ : x ∈ xs) →
  ∈-++⁻ {ys = ys} (∈-++⁺ˡ x∈) ≡ inj₁ x∈
∈-++⁻∘∈-++⁺ˡ = λ where
  (here _)  → refl
  (there _) → cong (there <$>₁_) (∈-++⁻∘∈-++⁺ˡ _)

∈-++⁻∘∈-++⁺ʳ : ∀ {x : A} (x∈ : x ∈ ys) →
  ∈-++⁻ {xs = xs} (∈-++⁺ʳ x∈) ≡ inj₂ x∈
∈-++⁻∘∈-++⁺ʳ {xs = []}    _ = refl
∈-++⁻∘∈-++⁺ʳ {xs = _ ∷ _} _ = cong (there <$>₁_) (∈-++⁻∘∈-++⁺ʳ _)

destruct-∈-++⁻ : ∀ {x : A} (x∈ : x ∈ xs ++ ys) →
  case ∈-++⁻ {xs = xs} x∈ of λ where
    (inj₁ x∈ˡ) → x∈ ≡ ∈-++⁺ˡ x∈ˡ
    (inj₂ x∈ʳ) → x∈ ≡ ∈-++⁺ʳ x∈ʳ
destruct-∈-++⁻ {xs = []} {ys} x∈ = refl
destruct-∈-++⁻ {xs = x ∷ xs} {ys} (here x₁) = refl
destruct-∈-++⁻ {xs = x ∷ xs} {ys} (there x∈)
  with IH ← destruct-∈-++⁻ {xs = xs}{ys} x∈
  with ∈-++⁻ {xs = xs} x∈
... | inj₁ x∈ˡ = cong there IH
... | inj₂ x∈ʳ = cong there IH
