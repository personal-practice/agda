module Frobenius where

open import Prelude.Init

postulate
  A : Set
  μ : A × A → A
  Δ : A → A × A

f : A → A
f x = let x₁ , x₂ = Δ x
          x₁₁ , x₁₂ = Δ x₁
          x₁′ = μ (x₁₁ , x₁₂)
          x₁₁′ , x₁₂′ = Δ x₁′
          x₁″ = μ (x₁₁′ , x₁₂′)
      in  μ (x₁″ , x₂)
  -- f = ⨀ ∘ ⨀ ∣ ↑


-- record Monoid (A : Set) : Set where
--   field
--     unit : ⊤ → A
--     -- μ  : A × A → A
--     _⊗_  : A → A → A
-- open Monoid ⦃...⦄

-- record Comonoid (A : Set) : Set where
--   field
--     counit : A → ⊤
--     ⊚_  : A → A × A
-- open Comonoid ⦃...⦄

-- record Frobenius (A : Set) : Set where
--   field
--     ⦃ mon   ⦄ : Monoid A
--     ⦃ comon ⦄ : Comonoid A
-- open Frobenius ⦃...⦄

-- module _ (A : Set) ⦃ _ : Frobenius A ⦄ where

--   _≫_ : Op₂ (A → A)
--   f ≫ g = g ∘ f

--   ↑ : Op₁ A
--   ↑ x = x

--   _∣_ : Op₂ (A → A)
--   (fˡ ∣ fʳ) x = let x₁ , x₂ = ⊚ x
--                 in  fˡ x₁ ⊗ fʳ x₂

--   ⨀ ⨀ʳ ⨀ˡ ⨀ˡ² : Op₁ A
--   ⨀ = ↑ ∣ ↑

--   ⨀ʳ x = let x₁ , x₂ = ⊚ x
--          in  ((x₁ ⊗_) ∣ ↑) x₂

--   ⨀ˡ x = let x₁ , x₂ = ⊚ x
--          in  (↑ ∣ (_⊗ x₂)) x₁

--   -- ⨀ˡ² x = let x₁ , x₂ = ⊚ x
--   --             x₁₁ , x₁₂ = ⊚ x₁
--   --             x₁₁₁ , x₁₁₂ = ⊚ x₁₁
--   --         in x₁₁₁ ⊗ (x₁₁₂ ⊗ (x₁₂ ⊗ x₂))
--   ⨀ˡ² x = let x₁ , x₂ = ⊚ x
--               x₁₁ , x₁₂ = ⊚ x₁
--           in (↑ ∣ (_⊗ (x₁₂ ⊗ x₂))) x₁₁

--   f : A → A
--   -- f x = let x₁ , x₂ = ⊚ x
--   --           x₁₁ , x₁₂ = ⊚ x₁
--   --           x₁′ = x₁₁ ⊗ x₁₂
--   --           x₁₁′ , x₁₂′ = ⊚ x₁′
--   --           x₁″ = x₁₁′ ⊗ x₁₂′
--   --       in  x₁″ ⊗ x₂
--   f = ⨀ ∘ ⨀ ∣ ↑

--   -- D³₂

--   abcabc = ⨀ ≫ ⨀

--   abacbc : A → A
--   -- abacbc x =
--   --   let x₁ , x₂ = ⊚ x
--   --       x₂₁ , x₂₂ = ⊚ x₂
--   --   in (x₁ ⊗ x₂₁) ⊗ x₂₂

--   -- abacbc x =
--   --   let x₁ , x₂ = ⊚ x
--   --   in ((x₁ ⊗_) ∣ ↑) x₂

--   abacbc = ⨀ʳ

--   aabbcc = ⨀ˡ

--   ababcc = ↑ ∣ ⨀
--   aabcbc = ⨀ ∣ ↑



--   -- data Op : Set where

--   -- ⟦_⟧ : Op → (A → A)
--   -- ⟦ op ⟧ = {!!}
