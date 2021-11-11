module ImplicitsVsModule where

open import Prelude.Init
open import Prelude.Lists

p× : ∀ {xs : List Bool}
  → Σ[ i ∈ Index xs ]
      (L.lookup xs i ≡ true) × (xs ≡ (false ∷ []))
  → ⊥
-- 1) works
p× (0F , () , refl)
-- 2) works
p× = λ where (0F , () , refl)
-- 3) works
p× x = case x of λ where (0F , () , refl)
-- 4) works
p× {xs} (i , x≡ , xs≡) = case (Σ[ i ∈ Index xs ] (L.lookup xs i ≡ true) × (xs ≡ (false ∷ []))) ∋ (i , x≡ , xs≡) of λ where (0F , () , refl)
-- 5) error
-- p× {xs} (i , x≡ , xs≡) = case (i , x≡ , xs≡) of λ where (0F , () , refl) -- 4) error

p : ∀ {xs : List Bool} {i : Fin (length xs)} → L.lookup xs i ≡ true → xs ≢ (false ∷ [])
p {i = 0F} () refl
-- p {i = i} x≡ xs≡ = case (xs≡ , i ,′ x≡) of λ where (refl , zero , ())

module _ {xs : List Bool} {i : Fin (length xs)} where
  p′ : L.lookup xs i ≡ true → xs ≢ (false ∷ [])
  p′ x≡ xs≡ = case (Σ[ i ∈ Index xs ] (L.lookup xs i ≡ true) × (xs ≡ (false ∷ []))) ∋ (i , x≡ , xs≡) of λ where (0F , () , refl)
