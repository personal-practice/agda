module SugarMember where

open import Prelude.Init
open L.Mem

variable
  A : Set
  x y z w : A
  xs ys zs ws vs : List A

infix -1 _⇒_∣_
_⇒_∣_ : ∀ {C : Set} → x ∈ xs ++ ys → (x ∈ xs → C) → (x ∈ ys → C) → C
x∈ ⇒ f ∣ g = {!!}

infixr 6 _∥_
_∥_ : ∀ {C : Set} → (x ∈ xs → C) → (x ∈ ys → C) → (x ∈ xs ++ ys → C)
(f ∥ g) x∈ = case ∈-++⁻ _ x∈ of λ where
  (inj₁ x∈ˡ) → f x∈ˡ
  (inj₂ x∈ʳ) → g x∈ʳ

f : x ∉ xs → x ∉ zs → x ∉ ws
  → x ∈ xs ++ (ys ++ zs) ++ ws → x ∈ vs ++ ys
f {x = x}{xs}{zs}{ws}{ys}{vs} x∉xs x∉zs x∉ws x∈ =
  x∈ |> ⊥-elim ∘ x∉xs
      ∥ (∈-++⁺ʳ vs {ys} ∥ ⊥-elim ∘ x∉zs)
      ∥ ⊥-elim ∘ x∉ws
  -- case ∈-++⁻ (xs `++ ys `++ zs) {ws} x∈ of λ where
  --   (inj₂ x∈ws) → ⊥-elim $ x∉ws x∈ws
  --   (inj₁ x∈′)  →
  --     case ∈-++⁻ (xs ++ ys) {zs} x∈′ of λ where
  --       (inj₂ x∈zs) → ⊥-elim $ x∉zs x∈zs
  --       (inj₁ x∈″)  →
  --         case ∈-++⁻ xs {ys} x∈″ of λ where
  --           (inj₁ x∈xs) → ⊥-elim $ x∉xs x∈xs
  --           (inj₂ x∈ys) → ∈-++⁺ʳ vs {ys} x∈ys
