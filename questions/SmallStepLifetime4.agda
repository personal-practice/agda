module SmallStepLifetime4 where

open import Prelude.Init
open import Prelude.Membership
open import Prelude.Lists
open import Prelude.Nary
open import Prelude.Nary
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.General
-- open import Prelude.Closures

-------------------------------------------------------

module ReflexiveTransitiveClosure {A : Set} (_—→_ : Rel₀ A) where

  private variable x y z : A

  -- left-biased
  infix -1 _—↠_
  data _—↠_ : Rel₀ A where
    _∎ : ∀ x → x —↠ x
    _—→⟨_⟩_ : ∀ x → x —→ y → y —↠ z → x —↠ z

  infix  3 _∎
  infixr 2 _—→⟨_⟩_
  infix  1 begin_
  pattern begin_ x = x

  -- right-biased view
  _←—_ : Rel₀ A
  _←—_ = flip _—→_

  infixr 2 _`⟨_⟩←—_
  _`⟨_⟩←—_ : ∀ z → y —→ z → x —↠ y → x —↠ z
  _ `⟨ st ⟩←— (_ ∎)           = _ —→⟨ st ⟩ _ ∎
  _ `⟨ st ⟩←— (_ —→⟨ st′ ⟩ p) = _ —→⟨ st′ ⟩ (_ `⟨ st ⟩←— p)

  infix -1 _↞—_
  -- data _↞—_ : Rel A ℓ where
  --   _∎ : ∀ x → x ↞— x
  --   _⟨_⟩←—_ : ∀ z → z ←— y → y ↞— x → z ↞— x
  data _↞—_ : (y x : A) → Pred₀ (x —↠ y) where
    _∎ : ∀ x → (x ↞— x) (x ∎)
    _⟨_⟩←—_ : ∀ {x y} {x↠ : x —↠ y} z → (y→z : z ←— y) → (y ↞— x) x↠ → (z ↞— x) (z `⟨ y→z ⟩←— x↠)

  -- infix  3 _∎
  infixr 2 _⟨_⟩←—_

--   -- view correspondence
--   viewLeft : x —↠ y → y ↞— x
--   viewLeft (_ ∎)          = _ ∎
--   viewLeft (_ —→⟨ st ⟩ p) = _ `—→⟨ st ⟩ viewLeft p
--     where
--       infixr 2 _`—→⟨_⟩_
--       _`—→⟨_⟩_ : ∀ x → y ←— x → z ↞— y → z ↞— x
--       _ `—→⟨ st ⟩ _ ∎           = _ ⟨ st ⟩←— _ ∎
--       _ `—→⟨ st ⟩ _ ⟨ st′ ⟩←— p = _ ⟨ st′ ⟩←— _ `—→⟨ st ⟩ p

--   viewRight : y ↞— x → x —↠ y
--   viewRight (_ ∎)          = _ ∎
--   viewRight (_ ⟨ st ⟩←— p) = _ `⟨ st ⟩←— viewRight p
--     where
--       infixr 2 _`⟨_⟩←—_
--       _`⟨_⟩←—_ : ∀ z → y —→ z → x —↠ y → x —↠ z
--       _ `⟨ st ⟩←— (_ ∎)           = _ —→⟨ st ⟩ _ ∎
--       _ `⟨ st ⟩←— (_ —→⟨ st′ ⟩ p) = _ —→⟨ st′ ⟩ (_ `⟨ st ⟩←— p)

--   view↔ : (x —↠ y) ↔ (y ↞— x)
--   view↔ = viewLeft , viewRight

-- -- private
-- --   variable n : ℕ

-- --   infix -1 _—→_
-- --   data _—→_ : Rel₀ ℕ where
-- --     [inc] : n —→ suc n
-- --     [dec] : suc n —→ n

-- --   open ReflexiveTransitiveClosure _—→_

-- --   _ : 10 —↠ 12
-- --   _ = begin
-- --     10 —→⟨ [inc] ⟩
-- --     11 —→⟨ [dec] ⟩
-- --     10 —→⟨ [inc] ⟩
-- --     11 —→⟨ [inc] ⟩
-- --     12 ∎

-- --   _ : 12 ↞— 10
-- --   _ = begin
-- --     12 ⟨ [inc] ⟩←—
-- --     11 ⟨ [dec] ⟩←—
-- --     12 ⟨ [inc] ⟩←—
-- --     11 ⟨ [inc] ⟩←—
-- --     10 ∎

-- -- ---------------------------------------------------------------

-- -- pattern 𝟙  = here refl
-- -- pattern 𝟚  = there 𝟙
-- -- pattern 𝟛  = there 𝟚

-- -- data ℂ : Set where
-- --   ∅ : ℂ
-- --   _∣_ : Op₂ ℂ
-- --   ⁇_ : List ℕ → ℂ
-- --   R : ℕ → ℂ
-- --   ◆_ : List ℕ → ℂ

-- -- infixr 4 _∣_
-- -- infix 5 ⁇_ ◆_

-- -- variable
-- --   A : Set ℓ
-- --   c c′ c″ Γ Γ′ Γ″ Δ Δ′ Δ″ :  ℂ
-- --   n n′ : ℕ
-- --   ns ns′ rs rs′ : List ℕ

-- -- P : Pred₀ ℕ
-- -- P = _≤ 10

-- -- responses : ℂ → List ℕ
-- -- responses = λ where
-- --   (R r)   → [ r ]
-- --   (l ∣ r) → responses l ++ responses r
-- --   _       → []

-- -- infix -1 _—→_
-- -- data _—→_ : ℂ → ℂ → Set where

-- --   [Query] :
-- --     ∅ —→ ⁇ ns ∣ ∅

-- --   [Prove] :
-- --       (n ∈ ns) → P n
-- --       --————————————————————————
-- --     → ⁇ ns ∣ Γ —→ ⁇ ns ∣ Γ ∣ R n

-- --   [QED] :
-- --       responses Δ ↭ ns
-- --       --————————————————————————
-- --     → ⁇ ns ∣ Δ —→ ◆ ns

-- -- open ReflexiveTransitiveClosure _—→_

-- -- _ : ∅ —↠ ◆ ⟦ 1 , 10 , 8 ⟧
-- -- _ = ∅
-- --   —→⟨ [Query] ⟩
-- --     ⁇ ⟦ 1 , 10 , 8 ⟧ ∣ ∅
-- --   —→⟨ [Prove] 𝟙 auto ⟩
-- --     ⁇ ⟦ 1 , 10 , 8 ⟧ ∣ ∅ ∣ R 1
-- --   —→⟨ [Prove] 𝟛 auto ⟩
-- --     ⁇ ⟦ 1 , 10 , 8 ⟧ ∣ (∅ ∣ R 1) ∣ R 8
-- --   —→⟨ [Prove] 𝟚 auto ⟩
-- --     ⁇ ⟦ 1 , 10 , 8 ⟧ ∣ ((∅ ∣ R 1) ∣ R 8) ∣ R 10
-- --   —→⟨ [QED] auto ⟩
-- --     ◆ ⟦ 1 , 10 , 8 ⟧
-- --   ∎

-- -- _ : ◆ ⟦ 1 , 10 , 8 ⟧ ↞— ∅
-- -- _ = ◆ ⟦ 1 , 10 , 8 ⟧
-- --   ⟨ [QED] auto ⟩←—
-- --     ⁇ ⟦ 1 , 10 , 8 ⟧ ∣ ((∅ ∣ R 1) ∣ R 8) ∣ R 10
-- --   ⟨ [Prove] 𝟚 auto ⟩←—
-- --     ⁇ ⟦ 1 , 10 , 8 ⟧ ∣ (∅ ∣ R 1) ∣ R 8
-- --   ⟨ [Prove] 𝟛 auto ⟩←—
-- --     ⁇ ⟦ 1 , 10 , 8 ⟧ ∣ ∅ ∣ R 1
-- --   ⟨ [Prove] 𝟙 auto ⟩←—
-- --     ⁇ ⟦ 1 , 10 , 8 ⟧ ∣ ∅
-- --   ⟨ [Query] ⟩←—
-- --     ∅
-- --   ∎

-- -- {-
-- -- -- NB: if we do induction on the left-view of our closure (ie. _—↠_) we get stuck
-- -- lemma :
-- --     ∅ —↠ Δ
-- --     --————————————————————————
-- --   → All P (responses Δ)
-- -- lemma tr with tr
-- -- ... | .∅ ∎ = []
-- -- ... | _ —→⟨ [Query] ⟩ _ = {!!}
-- -- -}

-- -- -- [WORKAROUND] do induction on the snoc-view, and just use view on the argument to recover our initial lemma
-- -- -- NB: one would need to also use "unview" if the return type mentioned our step relation.
-- -- lemma′ :
-- --     Δ ↞— ∅
-- --     --————————————————————————
-- --   → All P (responses Δ)
-- -- lemma′ tr with tr
-- -- ... | .∅ ∎ = []
-- -- ... | _ ⟨ [Query] ⟩←— _ = []
-- -- ... | _ ⟨ [Prove] {n = n} n∈ Pₙ ⟩←— tr′
-- --     = L.All.++⁺ (lemma′ tr′) (Pₙ ∷ [])
-- -- ... | _ ⟨ [QED] _ ⟩←— _ = []

-- -- lemma :
-- --     ∅ —↠ Δ
-- --     --————————————————————————
-- --   → All P (responses Δ)
-- -- lemma = lemma′ ∘ viewLeft

-- -- theorem :
-- --     ∅ —↠ ◆ rs
-- --     --————————————————————————
-- --   → All P rs
-- -- theorem tr with viewLeft tr
-- -- ... | .(◆ _) ⟨ [QED] {ns = ns} p ⟩←— tr′
-- --   with tr′
-- -- ... | .(⁇ _ ∣ ∅) ⟨ [Query] ⟩←— _ = L.Perm.All-resp-↭ p []
-- -- ... | .(⁇ ns ∣ _ ∣ R n) ⟨ [Prove] {n = n} n∈ Pₙ ⟩←— tr″
-- --     = L.Perm.All-resp-↭ p (L.All.++⁺ (lemma (viewRight tr″)) (Pₙ ∷ []))
