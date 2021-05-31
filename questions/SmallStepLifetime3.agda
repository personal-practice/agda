module SmallStepLifetime3 where

open import Prelude.Init
open import Prelude.Membership
open import Prelude.Lists
open import Prelude.Nary
open import Prelude.Nary
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.General
open import Prelude.Closures

pattern 𝟙  = here refl
pattern 𝟚  = there 𝟙
pattern 𝟛  = there 𝟚

data ℂ : Set where
  ∅ : ℂ
  _∣_ : Op₂ ℂ
  ⁇_ : List ℕ → ℂ
  R : ℕ → ℂ
  ◆_ : List ℕ → ℂ

infixr 4 _∣_
infix 5 ⁇_ ◆_

variable
  A : Set ℓ
  c c′ c″ Γ Γ′ Γ″ Δ Δ′ Δ″ :  ℂ
  n n′ : ℕ
  ns ns′ rs rs′ : List ℕ

P : Pred₀ ℕ
P = _≤ 10

responses : ℂ → List ℕ
responses = λ where
  (R r)   → [ r ]
  (l ∣ r) → responses l ++ responses r
  _       → []

infix -1 _—→_
data _—→_ : ℂ → ℂ → Set where

  [Query] :
    ∅ —→ ⁇ ns ∣ ∅

  [Prove] :
      (n ∈ ns) → P n
      --————————————————————————
    → ⁇ ns ∣ Γ —→ ⁇ ns ∣ Γ ∣ R n

  [QED] :
      responses Δ ↭ ns
      --————————————————————————
    → ⁇ ns ∣ Δ —→ ◆ ns

open ReflexiveTransitiveClosure _—→_

_ : ∅ —↠ ◆ ⟦ 1 , 10 , 8 ⟧
_ = ∅
  —→⟨ [Query] ⟩
    ⁇ ⟦ 1 , 10 , 8 ⟧ ∣ ∅
  —→⟨ [Prove] 𝟙 auto ⟩
    ⁇ ⟦ 1 , 10 , 8 ⟧ ∣ ∅ ∣ R 1
  —→⟨ [Prove] 𝟛 auto ⟩
    ⁇ ⟦ 1 , 10 , 8 ⟧ ∣ (∅ ∣ R 1) ∣ R 8
  —→⟨ [Prove] 𝟚 auto ⟩
    ⁇ ⟦ 1 , 10 , 8 ⟧ ∣ ((∅ ∣ R 1) ∣ R 8) ∣ R 10
  —→⟨ [QED] auto ⟩
    ◆ ⟦ 1 , 10 , 8 ⟧
  ∎

_ : ◆ ⟦ 1 , 10 , 8 ⟧ ↞— ∅
_ = ◆ ⟦ 1 , 10 , 8 ⟧
  ⟨ [QED] auto ⟩←—
    ⁇ ⟦ 1 , 10 , 8 ⟧ ∣ ((∅ ∣ R 1) ∣ R 8) ∣ R 10
  ⟨ [Prove] 𝟚 auto ⟩←—
    ⁇ ⟦ 1 , 10 , 8 ⟧ ∣ (∅ ∣ R 1) ∣ R 8
  ⟨ [Prove] 𝟛 auto ⟩←—
    ⁇ ⟦ 1 , 10 , 8 ⟧ ∣ ∅ ∣ R 1
  ⟨ [Prove] 𝟙 auto ⟩←—
    ⁇ ⟦ 1 , 10 , 8 ⟧ ∣ ∅
  ⟨ [Query] ⟩←—
    ∅
  ∎

lemma :
    ∅ —↠ Δ
    --————————————————————————
  → All P (responses Δ)
lemma tr with viewLeft tr
... | .∅ ∎ = []
... | _ ⟨ [Query] ⟩←— _ = []
... | _ ⟨ [Prove] {n = n} n∈ Pₙ ⟩←— tr′
    = L.All.++⁺ (lemma (viewRight tr′)) (Pₙ ∷ [])
... | _ ⟨ [QED] _ ⟩←— _ = []

theorem :
    ∅ —↠ ◆ rs
    --————————————————————————
  → All P rs
theorem tr with viewLeft tr
... | .(◆ _) ⟨ [QED] {ns = ns} p ⟩←— tr′
  with tr′
... | .(⁇ _ ∣ ∅) ⟨ [Query] ⟩←— _ = L.Perm.All-resp-↭ p []
... | .(⁇ ns ∣ _ ∣ R n) ⟨ [Prove] {n = n} n∈ Pₙ ⟩←— tr″
    = L.Perm.All-resp-↭ p (L.All.++⁺ (lemma (viewRight tr″)) (Pₙ ∷ []))
