module SmallStepLifetime where

open import Prelude.Init
open import Prelude.Membership
open import Prelude.Lists
open import Prelude.Nary
open import Prelude.Nary
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.General

pattern 𝟙⊥ = here ()
pattern 𝟙  = here refl
pattern 𝟚  = there 𝟙
pattern 𝟚⊥ = there ()
pattern 𝟛  = there 𝟚
pattern 𝟛⊥ = there (there ())

data Response (A : Set ℓ) : Set ℓ where
  Y N : A → Response A

data ℂ : Set where
  ∅ : ℂ
  _∣_ : Op₂ ℂ
  ⁇_ : List ℕ → ℂ
  R : Response ℕ → ℂ
  _∎ : List (Response ℕ) → ℂ

infixr 4 _∣_
infix 5 ⁇_
infix 5 _∎

pattern Rʸ x = R (Y x)
pattern Rⁿ x = R (N x)

variable
  A : Set ℓ
  c c′ c″ Γ Γ′ Γ″ Δ Δ′ Δ″ :  ℂ
  n n′ : ℕ
  ns ns′ : List ℕ
  rs : List (Response ℕ)

unwrap : Response A → A
unwrap = λ{ (Y x) → x; (N x) → x }

P : Pred₀ ℕ
P = _≤ 10

_-answers-_ : ℂ → List ℕ → Set
Δ -answers- ns with Δ
... | ∅     = ns ≡ []
... | R n   = ns ≡ [ unwrap n ]
... | l ∣ r = ∃[ nsˡ ] ∃[ nsʳ ]
  ( (l -answers- nsˡ)
  × (r -answers- nsʳ)
  × (ns ↭ nsˡ ++ nsʳ)
  )
... | ⁇ _ = ⊥
... | _ ∎ = ⊥

-- _-answers?-_ : ∀ Δ ns → (Δ -answers- ns) ⁇
-- Δ -answers?- ns with Δ
-- ... | ∅     = it
-- ... | R n   = it
-- ... | l ∣ r = {!!}
-- ... | ⁇ _ = it
-- ... | _ ∎ = it

answer : (Δ -answers- ns) → ns ↦ Response ℕ
answer {Δ = Δ} p with Δ | p
... | ∅     | refl = λ ()
... | R r   | refl = λ{ 𝟙 → r }
... | l ∣ r | nsˡ , nsʳ , (pˡ , pʳ , ns↭) = extend-↦ ns↭ (answer pˡ) (answer pʳ)

infix 0 _—→_
data _—→_ : ℂ → ℂ → Set where

  [Query] :
    ∅ —→ ⁇ ns ∣ ∅

  [Prove] :
      (n ∈ ns) → P n
      --————————————————————————
    → ⁇ ns ∣ Γ —→ ⁇ ns ∣ Γ ∣ R (Y n)

  [Refute] :
      (n ∈ ns) → ¬ P n
      --————————————————————————
    → ⁇ ns ∣ Γ —→ ⁇ ns ∣ Γ ∣ R (N n)

  [QED] :
      (p : Δ -answers- ns)
      --————————————————————————
    → ⁇ ns ∣ Δ —→ codom (answer p) ∎

infix -1 _—↠_
infixr -1 _—→⟨_⟩_
infix 0 _QED
data _—↠_ : ℂ → ℂ → Set where
  _QED : ∀ Γ → Γ —↠ Γ

  _—→⟨_⟩_ : ∀ (Γ : ℂ)
    → Γ —→ Γ′
    → Γ′ —↠ Γ″
      --————————————————————————
    → Γ —↠ Γ″

_ : ∅ —↠ (Y 1 ∷ Y 10 ∷ N 100 ∷ []) ∎
_ = ∅
  —→⟨ [Query] ⟩
    ⁇ ns_ ∣ ∅
  —→⟨ [Prove] 𝟙 auto ⟩
    ⁇ ns_ ∣ ∅ ∣ Rʸ 1
  —→⟨ [Refute] 𝟛 auto ⟩
    ⁇ ns_ ∣ (∅ ∣ Rʸ 1) ∣ Rⁿ 100
  —→⟨ [Prove] 𝟚 auto ⟩
    ⁇ ns_ ∣ ((∅ ∣ Rʸ 1) ∣ Rⁿ 100) ∣ Rʸ 10
  —→⟨ [QED] p ⟩
    (Y 1 ∷ Y 10 ∷ N 100 ∷ []) ∎
  QED
  where
    Δ_  = ((∅ ∣ Rʸ 1) ∣ Rⁿ 100) ∣ Rʸ 10
    ns_ = ⟦ 1 , 10 , 100 ⟧

    p : Δ_ -answers- ns_
    p = ⟦ 1 , 100 ⟧ , [ 10 ]
        , ([ 1 ] , [ 100 ] , ([] , [ 1 ] , auto , auto , auto) , auto , auto)
        , auto
        , auto

infixr -1 _`⟨_⟩←—_
_`⟨_⟩←—_ : ∀ (Γ″ : ℂ)
  → Γ′ —→ Γ″
  → Γ —↠ Γ′
    --———————————
  → Γ —↠ Γ″
Γ″ `⟨ Γ′→Γ″ ⟩←— (_ QED) = _ —→⟨ Γ′→Γ″ ⟩ Γ″ QED
Γ″ `⟨ Γ′→Γ″ ⟩←— (Δ —→⟨ Γ→Δ ⟩ Δ↠Γ′) =  Δ —→⟨ Γ→Δ ⟩ (Γ″ `⟨ Γ′→Γ″ ⟩←— Δ↠Γ′)

infix 0 _←—_
_←—_ : Rel₀ ℂ
_←—_ = flip _—→_

infix -1 _↞—_
infixr -1 _⟨_⟩←—_
-- infix 0 BEGIN_

data _↞—_ : ℂ → ℂ → Set where
  _QED : ∀ Γ → Γ ↞— Γ

  _⟨_⟩←—_ : ∀ (Γ : ℂ)
    → Γ ←— Γ′
    → Γ′ ↞— Γ″
      --————————————————————————
    → Γ ↞— Γ″

_ : (Y 1 ∷ Y 10 ∷ N 100 ∷ []) ∎ ↞— ∅
_ = (Y 1 ∷ Y 10 ∷ N 100 ∷ []) ∎
  ⟨ [QED] p ⟩←—
    ⁇ ns_ ∣ ((∅ ∣ Rʸ 1) ∣ Rⁿ 100) ∣ Rʸ 10
  ⟨ [Prove] 𝟚 auto ⟩←—
    ⁇ ns_ ∣ (∅ ∣ Rʸ 1) ∣ Rⁿ 100
  ⟨ [Refute] 𝟛 auto ⟩←—
    ⁇ ns_ ∣ ∅ ∣ Rʸ 1
  ⟨ [Prove] 𝟙 auto ⟩←—
    ⁇ ns_ ∣ ∅
  ⟨ [Query] ⟩←—
    ∅
  QED
  where
    Δ_  = ((∅ ∣ Rʸ 1) ∣ Rⁿ 100) ∣ Rʸ 10
    ns_ = ⟦ 1 , 10 , 100 ⟧

    p : Δ_ -answers- ns_
    p = ⟦ 1 , 100 ⟧ , [ 10 ]
        , ([ 1 ] , [ 100 ] , ([] , [ 1 ] , auto , auto , auto) , auto , auto)
        , auto
        , auto

infixr -1 _`—→⟨_⟩_
_`—→⟨_⟩_ : ∀ (Γ : ℂ)
  → Γ′ ←— Γ
  → Γ″ ↞— Γ′
    --———————————
  → Γ″ ↞— Γ
Γ `—→⟨ Γ→Γ′ ⟩ _ QED = _ ⟨ Γ→Γ′ ⟩←— _ QED
Γ `—→⟨ Γ→Γ′ ⟩ Δ ⟨ Δ→Γ″ ⟩←— Δ↠Γ′ = _ ⟨ Δ→Γ″ ⟩←— Γ `—→⟨ Γ→Γ′ ⟩ Δ↠Γ′

rightToLeft : Γ —↠ Γ′ → Γ′ ↞— Γ
rightToLeft (_ QED) = _ QED
rightToLeft (_ —→⟨ st ⟩ p) =  _ `—→⟨ st ⟩ rightToLeft p

leftToRight : Γ′ ↞— Γ → Γ —↠ Γ′
leftToRight (_ QED) = _ QED
leftToRight (_ ⟨ st ⟩←— p) = _ `⟨ st ⟩←— leftToRight p

equiv : (Γ —↠ Γ′) ↔ (Γ′ ↞— Γ)
equiv = rightToLeft , leftToRight

-- ∅—↠_ : Pred₀ ℂ
-- ∅—↠ = ∅ —↠_

-- _≈⋯_ : (Γ —↠ Γ″) (Γ′ —↠ Γ″) → Set
-- step ≈⋯ stepʳ = step ≡ —→

-- _≈_⋯ : (Γ —↠ Γ″) (Γ —↠ Γ′) → Set
-- step ≈ stepˡ ⋯ =

-- _≈_≫_ : (Γ —↠ Γ″) (Γ —↠ Γ′) (Γ′ —↠ Γ″) → Set
-- step ≈ stepˡ ≫ stepʳ =

Valid : Pred₀ (Response ℕ)
Valid (Y n) = P n
Valid (N n) = ¬ P n

qed→ :
    rs ∎ —↠ Γ′
    --————————————————————————
  → Γ′ ≡ rs ∎
qed→ (.(_ ∎) QED) = refl

theorem :
    ∅ —↠ rs ∎
    --————————————————————————
  → All Valid rs
theorem tr with rightToLeft tr
... | .(_ ∎) ⟨ [QED] p ⟩←— tr′
  with tr′ | p
... | .(⁇ _ ∣ ∅) ⟨ [Query] ⟩←— .∅ QED | refl = []
... | .(⁇ ns ∣ _ ∣ Rʸ _) ⟨ [Prove] {n}{ns} n∈ Pₙ ⟩←— trr | nsˡ , .(_ ∷ []) , pˡ , refl , ns↭ = qed
  where
    rs′ = codom $ extend-↦ ns↭ (answer pˡ) (answer {Δ = Rʸ _} refl)
    rs″ = Y n ∷ codom (answer pˡ)

    ns↭′ : ns ↭ n ∷ nsˡ
    ns↭′ = ↭-trans ns↭ (↭-sym $ L.Perm.∷↭∷ʳ n nsˡ)

    rs↭ : rs″ ↭ rs′
    rs↭ = {!L.Perm.∷↭∷ʳ (Y n) (codom $ answer pˡ)!}

    v : All Valid (codom $ answer pˡ)
    v = {!!}

    qed : All Valid rs′
    qed = L.Perm.All-resp-↭ rs↭ (Pₙ ∷ v)


{-
Goal: All Valid rs_
————————————————————————————————————————————————————————————
ns↭ : ns ↭ nsˡ ++ unwrap (Y n) ∷ []
pˡ  : Γ -answers- nsˡ
nsˡ : List ℕ
trr : ⁇ ns ∣ Γ ↞— ∅
tr′ : ⁇ ns ∣ Γ ∣ R (Y n) ↞— ∅
-}
... | .(⁇ _ ∣ _ ∣ Rⁿ _) ⟨ [Refute] n ¬Pₙ ⟩←— trr | pp = {!!}

-- theorem {[]} (.∅ —→⟨ [Query] {ns = ns} ⟩ .(⁇ ns ∣ ∅) —→⟨ x ⟩ step) = []
-- theorem {rs@(_ ∷ _)} (.∅ —→⟨ [Query] {ns = ns} ⟩ .(⁇ ns ∣ ∅) —→⟨ [Prove] {n = n} n∈ Pₙ ⟩ step)
--   = {!!}
-- theorem {rs@(_ ∷ _)} (.∅ —→⟨ [Query] {ns = ns} ⟩ .(⁇ ns ∣ ∅) —→⟨ [Refute] x x₁ ⟩ step) = {!!}
-- theorem {rs@(_ ∷ _)} (.∅ —→⟨ [Query] {ns = .[]} ⟩ .(⁇ [] ∣ ∅) —→⟨ [QED] refl ⟩ step) = case qed→ step of λ ()
{-
Goal: All Valid rs
————————————————————————————————————————————————————————————
step : Γ′ —↠ rs ∎
x    : ⁇ ns ∣ ∅ —→ Γ′
Γ′   : ℂ   (not in scope)
ns   : List ℕ
rs   : List (Response ℕ)
-}

record HasResponses (A : Set ℓ) : Set ℓ where
  field
    responses : A → List (Response ℕ)
open HasResponses ⦃ ... ⦄ public

instance
  HR-ℂ : HasResponses ℂ
  HR-ℂ .responses = λ where
    (R n)   → [ n ]
    (l ∣ r) → responses l ++ responses r
    _       → []

  HR-tr : HasResponses (Γ —↠ Γ′)
  HR-tr .responses = λ where
    (_ QED) → []
    (_ —→⟨ [Query] ⟩ tr) → responses tr
    (_ —→⟨ [Prove] {n = n} _ _ ⟩ tr)  → Y n ∷ responses tr
    (_ —→⟨ [Refute] {n = n} _ _ ⟩ tr) → N n ∷ responses tr
    (_ —→⟨ [QED] _ ⟩ .(_ ∎) QED) → []

lemma :
    (tr : Γ —↠ Γ′)
    --————————————————————————
  → All Valid (responses tr)
lemma (_ QED) = []
lemma (_ —→⟨ [Query] ⟩ tr) = lemma tr
lemma (_ —→⟨ [Prove] _ P ⟩ tr) = P ∷ lemma tr
lemma (_ —→⟨ [Refute] _ ¬P ⟩ tr) = ¬P ∷ lemma tr
lemma (_ —→⟨ [QED] _ ⟩ .(_ ∎) QED) = []

theorem′ :

    (tr : ∅ —↠ rs ∎)
    --————————————————————————
  → rs ↭ responses tr
theorem′ (.∅ —→⟨ [Query] ⟩ .(⁇ _ ∣ ∅) —→⟨ [Prove] x x₁ ⟩ tr) = {!!}
{-
Goal: rs ↭
      Y n ∷
      (λ { (_ QED) → []
         ; (_ —→⟨ [Query] ⟩ tr) → HasResponses.responses HR-tr tr
         ; (_ —→⟨ [Prove] {n = n₁} _ _ ⟩ tr)
             → Y n₁ ∷ HasResponses.responses HR-tr tr
         ; (_ —→⟨ [Refute] {n = n₁} _ _ ⟩ tr)
             → N n₁ ∷ HasResponses.responses HR-tr tr
         ; (_ —→⟨ [QED] _ ⟩ .(codom (answer _) ∎) QED) → []
         ; (.(⁇ _ ∣ ∅ ∣ R (Y _)) —→⟨ [QED] p ⟩
            .(codom (answer p) ∎) —→⟨ () ⟩ x₂)
         })
      tr
————————————————————————————————————————————————————————————
tr : ⁇ ns ∣ ∅ ∣ R (Y n) —↠ rs ∎
x₁ : P n
x  : (setoid ℕ Data.List.Membership.Setoid.∈ n) ns
n  : ℕ   (not in scope)
ns : List ℕ   (not in scope)
rs : List (Response ℕ)   (not in scope)
-}
theorem′ (.∅ —→⟨ [Query] ⟩ .(⁇ _ ∣ ∅) —→⟨ [Refute] x x₁ ⟩ tr) = {!!}
theorem′ (.∅ —→⟨ [Query] ⟩ .(⁇ [] ∣ ∅) —→⟨ [QED] refl ⟩ .([] ∎) QED) = ↭-refl



-- lastStep :

--     (step : ∅ —↠ rs ∎)
--     --————————————————————————
--   → step ≈ Γ′ —→⟨ [QED] p ⟩ rs ∎
--   × ∃[ Δ ] let Γₙ-₁ = ⁇ ns ∣ Δ in

{-
Initial Final : Pred₀ ℂ
Initial = λ{ (⁇ _) → ⊤; _ → ⊥ }
Final   = λ{ (_ ∎) → ⊤; _ → ⊥ }

record Trace : Set where
  field
    init fin : ℂ
    trace  : ∅ —↠ fin
    .isInit : Initial init
    .isFin  : Final fin

open Trace public

query : Trace → List ℕ
query record {init = ⁇ ns} = ns

responses : Trace → List (Response ℕ)
responses record {fin = rs ∎} = rs

h :
    (t : Trace)
    --————————————————————————
  → query t ≡ map unwrap (responses t)
h record {init = ⁇ ns; fin = rs ∎; trace = t}
  with t
... | .(⁇ ns) —→⟨ () ⟩ tr
-}
  -- = ns≡
  -- where
  --   ns_ = query t
  --   rs_ = responses t

  --   ns≡ : ns_ ≡ map unwrap rs_
  --   ns≡ = {!!}

-- lifetime′ :
--   let ns = map unwrap rs
--       Γ₀ = ⁇ ns ∣ ∅
--       Γₙ = rs ∎
--   in

--     Γ₀ —↠ Γₙ
--     --————————————————————————
--   → ∃[ Δ ] let Γₙ-₁ = ⁇ ns ∣ Δ in
--       ( (Γ₀ —↠ Γₙ-₁)
--       × (Γₙ-₁ —→ Γₙ)
--       )
-- lifetime′ {rs} step with rs
-- ... | [] = ∅ , ( (_ QED) , [QED] refl)
-- ... | r ∷ rs′ = {!!}

-- lifetime :
--   let ns = map unwrap rs
--       Γ₀ = ⁇ ns ∣ ∅
--       Γₙ = rs ∎
--   in

--     ∅ —↠ Γₙ
--     --————————————————————————
--   → (∅ —→ Γ₀)
--   × ∃[ Δ ] let Γₙ-₁ = ⁇ ns ∣ Δ in
--       ( (Γ₀ —↠ Γₙ-₁)
--       × (Γₙ-₁ —→ Γₙ)
--       )
-- -- lifetime {rs} (.∅ —→⟨ [Query] {ns = .(map unwrap rs)} ⟩ step) = [Query] , lifetime′ {!!}
-- lifetime = {!!}
