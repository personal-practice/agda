module FinMeasure where

open import Prelude.Init
open import Prelude.Ord
open import Prelude.General
open import Prelude.Measurable

private variable
  n m n′ m′ : ℕ
  fn : Fin n
  fn′ : Fin n′
  fm : Fin m
  fm′ : Fin m′

instance
  M-Fin : Measurable (Fin n)
  M-Fin {n} .∣_∣ _ = n

  M-∃Fin : Measurable (∃ Fin)
  M-∃Fin .∣_∣ = proj₁

-- 𝕄Rel : ∀ {X Y : Set} ⦃ _ : Measurable X ⦄ ⦃ _ : Measurable Y ⦄ → X → Y → Set
-- 𝕄Rel =

-- data Acc′ {X : Set} ⦃ _ : Measurable X ⦄ (x : X) : Set₁ where
--   acc :
--     (∀ {Y : Set} ⦃ _ : Measurable Y ⦄ (y : Y) → y ≺ᵐ x → Acc′ y)
--     ────────────────────────────────────────────────────────
--     Acc′ x

-- WellFounded′ : Set₁
-- WellFounded′ = ∀ {X : Set} ⦃ _ : Measurable X ⦄ (x : X) → Acc′ x


-- ≺ᵐ-wf : WellFounded′
-- ≺ᵐ-wf x = acc (go x)
--   where
--     go : ∀ {X : Set} ⦃ _ : Measurable X ⦄ (x : X)
--            {Y : Set} ⦃ _ : Measurable Y ⦄ (y : Y)
--        → y ≺ᵐ x
--        → Acc′ y
--     go x y y≺ with ∣ x ∣ | ∣ y ∣
--     ... | = {!!}


f : Fin n → Fin Nat.⌊ n /2⌋
f {n} fn = go _ (≺-wf fn)
  where
    go : ∀ (fn : Fin n) → Acc _≺_ fn
