open import Prelude.Init hiding ([_]); open SetAsType
open L.Mem
open import Prelude.General
open import Prelude.InferenceRules
open import Prelude.Closures
open import Prelude.Decidable
open import Prelude.DecEq hiding (_≠_)
open import Prelude.Ord
open import Prelude.Nary
open import Prelude.Lists.Indexed

private variable A B : Type; P : Pred₀ A

-- ** Core Verse calculus

data Primop : Type where
  gt add ♯map : Primop

Var = String

mutual
  Values = List Value

  data Value : Type where
    𝕧 : Var → Value
    𝕜 : ℕ → Value
    ♯ : Primop → Value
    ⟨_⟩ : Values → Value
    ƛ_⇒_ : Var → Expr → Value

  data Expr : Type where
    `_ : Value → Expr
    _⨾_ : ＝Expr → Expr → Expr
    ∃_⇒_ : Var → Expr → Expr
    fail : Expr
    _∣_ : Expr → Expr → Expr
    _·_ : Value → Value → Expr
    one⦅_⦆ all⦅_⦆ : Expr → Expr

  data ＝Expr : Type where
    _＝_ : Value → Expr → ＝Expr
    ≠_ : Expr → ＝Expr

infixr 2 ∃_⇒_ ƛ_⇒_
infixr 3 _∣_
infixr 4 _⨾_
infix  5 _＝_ _＝`_
pattern _＝`_ v v′ = v ＝ ` v′

pattern `𝕧 x = ` 𝕧 x
pattern `𝕜 x = ` 𝕜 x
pattern 𝕜0 = 𝕜 0; pattern 𝕜1 = 𝕜 1; pattern 𝕜2 = 𝕜 2; pattern 𝕜3 = 𝕜 3
pattern `⟨_⟩ x = ` ⟨ x ⟩
pattern ⟨⟩ = ⟨ [] ⟩
pattern `⟨⟩ = ` ⟨⟩

isConstant isScalar isTup isHeap isHead : Pred₀ Value
isConstant = λ where
  (𝕜 _) → ⊤
  _ → ⊥
isScalar = λ where
  (𝕧 _) → ⊤
  (𝕜 _) → ⊤
  (♯ _) → ⊤
  _ → ⊥
isTup = λ where
  ⟨ _ ⟩ → ⊤
  _ → ⊥
isHeap = λ where
  ⟨ _ ⟩ → ⊤
  (ƛ _ ⇒ _) → ⊤
  _ → ⊥
-- isHead = isHeap Unary.∪ isConstant
isHead = λ where
  ⟨ _ ⟩ → ⊤
  (ƛ _ ⇒ _) → ⊤
  (𝕜 _) → ⊤
  _ → ⊥

isConstant? : Decidable¹ isConstant
isConstant? = λ where
  (𝕜 _) → yes tt
  (𝕧 _) → no λ ()
  (♯ _) → no λ ()
  ⟨ _ ⟩ → no λ ()
  (ƛ _ ⇒ _) → no λ ()
isScalar? : Decidable¹ isScalar
isScalar? = λ where
  (𝕧 _) → yes tt
  (𝕜 _) → yes tt
  (♯ _) → yes tt
  ⟨ _ ⟩ → no λ ()
  (ƛ _ ⇒ _) → no λ ()
isTup? : Decidable¹ isTup
isTup? = λ where
  ⟨ _ ⟩ → yes tt
  (𝕜 _) → no λ ()
  (𝕧 _) → no λ ()
  (♯ _) → no λ ()
  (ƛ _ ⇒ _) → no λ ()
isHeap? : Decidable¹ isHeap
isHeap? = λ where
  ⟨ _ ⟩ → yes tt
  (ƛ _ ⇒ _) → yes tt
  (𝕜 _) → no λ ()
  (𝕧 _) → no λ ()
  (♯ _) → no λ ()
isHead? : Decidable¹ isHead
isHead? = λ where
  ⟨ _ ⟩ → yes tt
  (ƛ _ ⇒ _) → yes tt
  (𝕜 _) → yes tt
  (𝕧 _) → no λ ()
  (♯ _) → no λ ()

_ : Expr
_ = ∃ "x" ⇒ ≠ (∃ "y" ⇒ `⟨ ⟦ 𝕜2    , 𝕧 "y" ⟧ ⟩) ⨾
            ≠ (∃ "z" ⇒ `⟨ ⟦ 𝕧 "y" , 𝕜3    ⟧ ⟩) ⨾
            `𝕧 "x"

-- ** helpers

private variable
  e e′ e₁ e₂ : Expr
  eu eu′ : ＝Expr
  v v₁ v₂ v₁′ v₂′ : Value
  vs : Values
  s s′ : Value
  hnf hnf₁ hnf₂ : Value
  x y : Var
  k₁ k₂ n : ℕ

eu≠_ : Pred₀ ＝Expr
eu≠_ = λ where
  (𝕧 _ ＝` _) → ⊥
  _ → ⊤

≠[] : Pred₀ (List A)
≠[] = λ where
  [] → ⊥
  (_ ∷ _) → ⊤

∣⁺_ : (vs : Values) ⦃ _ : ≠[] vs ⦄ → Expr
∣⁺_ = λ where
  (v ∷ []) → ` v
  (v ∷ vs@(_ ∷ _)) → ` v ∣ ∣⁺ vs

enum-∣ : Var → (vs : Values) ⦃ _ : ≠[] vs ⦄ → Expr
enum-∣ x vs = go 0 vs
  where
    go : ℕ → (vs : Values) ⦃ _ : ≠[] vs ⦄ → Expr
    go i = let x＝i = 𝕧 x ＝` 𝕜 i in λ where
      (v ∷ []) → x＝i ⨾ ` v
      (v ∷ vs@(_ ∷ _)) → x＝i ⨾ ` v ∣ go (suc i) vs

-- ** free variables
record HasVars (A : Type) : Type where
  field fv : A → List Var
  fvs : List A → List Var
  fvs = concatMap fv
open HasVars ⦃...⦄ public

mutual instance
  hv : HasVars Var
  hv .fv x = x ∷ []

  hv× : ⦃ HasVars A ⦄ → ⦃ ∀ {a} → HasVars (P a) ⦄
      → HasVars (Σ A P)
  hv× .fv (a , b) = fv a ++ fv b

  hvv : HasVars Value
  hvv .fv = λ where
    (𝕧 x) → x ∷ []
    (𝕜 _) → []
    (♯ _) → []
    ⟨ vs ⟩ → fvs vs
    (ƛ x ⇒ e) → filter (¬? ∘ (_≟ x)) (fv e)

  {-# TERMINATING #-}
  hve : HasVars Expr
  hve .fv = λ where
    (` _) → []
    (e ⨾ e′) → fv (e , e′)
    (∃ x ⇒ e) → filter (¬? ∘ (_≟ x)) (fv e)
    fail → []
    (e ∣ e′) → fv (e , e′)
    (v · v′) → fv (v , v′)
    one⦅ e ⦆ → fv e
    all⦅ e ⦆ → fv e

  hv＝e : HasVars ＝Expr
  hv＝e .fv = λ where
    (v ＝ e) → fv (v , e)
    (≠ e) → fv e

-- ** choices
mutual
  data ∅Expr : Type where
    `_ : Value → ∅Expr
    _⨾_ : ＝∅Expr → ∅Expr → ∅Expr
    one⦅_⦆ all⦅_⦆ : ∅Expr → ∅Expr
    _⦅_⦆ : Primop → Value → ∅Expr
    ∃_⇒_ : Var → ∅Expr → ∅Expr
  data ＝∅Expr : Type where
    _＝_ : Value → ∅Expr → ＝∅Expr
    ≠_ : ∅Expr → ＝∅Expr

mutual
  data CX : Type where
    ∙ : CX
    _∙⨾_ : ＝CX → Expr → CX
    _⨾∙_ : ＝∅Expr → CX → CX
    ∃_⇒∙_ : Var → CX → CX

  data ＝CX : Type where
    ≠_ : CX → ＝CX
    _＝∙_ : Value → CX → ＝CX

variable cx cx′ : CX

_≠∙ : Pred₀ CX
_≠∙ = λ where ∙ → ⊥; _ → ⊤

mutual
  ∅→ : ∅Expr → Expr
  ∅→ = λ where
    (` v) → (` v)
    (e ⨾ e′) → ∅→＝ e ⨾ ∅→ e′
    one⦅ e ⦆ → ∅→ e
    all⦅ e ⦆ → ∅→ e
    (op ⦅ v ⦆) → ♯ op · ⟨ v ∷ [] ⟩
    (∃ x ⇒ e) → ∃ x ⇒ ∅→ e

  ∅→＝ : ＝∅Expr → ＝Expr
  ∅→＝ = λ where
    (v ＝ e) → v ＝ ∅→ e
    (≠ e) → ≠ (∅→ e)

mutual
  _[_] : CX → Expr → Expr
  ∙ [ e ] = e
  (cx ∙⨾ e′) [ e ] = cx ＝[ e ] ⨾ e′
  (ce ⨾∙ cx) [ e ] = ∅→＝ ce ⨾ cx [ e ]
  (∃ x ⇒∙ cx) [ e ] = ∃ x ⇒ cx [ e ]

  _＝[_] : ＝CX → Expr → ＝Expr
  (≠ cx) ＝[ e ] = ≠ (cx [ e ])
  (v ＝∙ cx) ＝[ e ] = v ＝ (cx [ e ])

-- ** Unification rewrite rules

_—↛⟨U-SCALAR⟩_ _—↛⟨U-TUP⟩_ : Rel₀ Value
_—↛⟨U-SCALAR⟩_ = λ where
  (𝕜 s) (𝕜 s′) → s ≡ s′
  _ _ → ⊥
v —↛⟨U-TUP⟩ v′ = isTup v × isTup v′

_—↛⟨U-SCALAR⟩?_ : Decidable² _—↛⟨U-SCALAR⟩_
_—↛⟨U-SCALAR⟩?_ = λ where
  (𝕜 s) → λ where
    (𝕜 s′) → s ≟ s′
    (𝕧 _) → no λ ()
    (♯ _) → no λ ()
    ⟨ _ ⟩ → no λ ()
    (ƛ _ ⇒ _) → no λ ()
  (𝕧 _) _ → no λ ()
  (♯ _) _ → no λ ()
  ⟨ _ ⟩ _ → no λ ()
  (ƛ _ ⇒ _) _ → no λ ()

_—↛⟨U-TUP⟩?_ : Decidable² _—↛⟨U-TUP⟩_
v —↛⟨U-TUP⟩? v′
  with isTup? v
... | no ¬tv = no (¬tv ∘ proj₁)
... | yes tv
  with isTup? v′
... | no ¬tv′ = no (¬tv′ ∘ proj₂)
... | yes tv′ = yes (tv , tv′)

mutual
  infix 0 _—→_ _≠—→≠_

  data _≠—→≠_ : Rel₀ Expr where

    U-SCALAR : ⦃ _ : isConstant s ⦄ →
      s ＝` s ⨾ e
      ≠—→≠
      e

    U-TUP :
      ⟨ ⟦ v₁ , v₂ ⟧ ⟩ ＝` ⟨ ⟦ v₁′ , v₂′ ⟧ ⟩ ⨾ e
      ≠—→≠
      (v₁ ＝` v₁′ ⨾ v₂ ＝` v₂′ ⨾ e)

    -- Application: 𝓐

    APP-BETA :
      x ∉ fv v
      ────────
      ((ƛ x ⇒ e) · v) ≠—→≠ (∃ x ⇒ 𝕧 x ＝` v ⨾ e)

    APP-TUP₀ :
      (⟨⟩ · v) ≠—→≠ fail

    APP-TUP : ⦃ _ : ≠[] vs ⦄ →
      x ∉ fv v
      ────────
      ⟨ vs ⟩ · v ≠—→≠ ∃ x ⇒ 𝕧 x ＝` v ⨾ enum-∣ x vs

    APP-ADD :
      (♯ add) · ⟨ ⟦ 𝕜 k₁ , 𝕜 k₂ ⟧ ⟩ ≠—→≠ `𝕜 (k₁ + k₂)

    APP-GT : {auto∶ k₁ > k₂} →
      (♯ gt) · ⟨ ⟦ 𝕜 k₁ , 𝕜 k₂ ⟧ ⟩ ≠—→≠ `𝕜 k₁

    APP-GT-FAIL : {auto∶ k₁ ≤ k₂} →
      (♯ gt) · ⟨ ⟦ 𝕜 k₁ , 𝕜 k₂ ⟧ ⟩ ≠—→≠ fail

    -- Normalization: 𝓝

    NORM-VAL :
      ≠ (` v) ⨾ e ≠—→≠ e

    NORM-SEQ-ASSOC :
      ≠ (eu ⨾ e₁) ⨾ e₂ ≠—→≠ eu ⨾ (≠ e₁ ⨾ e₂)

    NORM-SEQ-SWAP₁ :
      eu ⨾ (𝕧 x ＝` v ⨾ e) ≠—→≠ 𝕧 x ＝` v ⨾ (eu ⨾ e)

    -- NORM-SEQ-SWAP₂ : ⦃ _ : ≠ e ⦄ ⦃ _ : eu≠ eu ⦄ →
    --   eu ⨾ (𝕧 x ＝` s ⨾ e) —→ 𝕧 x ＝` s ⨾ (eu ⨾ e)

    NORM-SEQ-DEFR :
      x ∉ fv e₂
      ─────────
      ≠ (∃ x ⇒ e₁) ⨾ e₂ ≠—→≠ ∃ x ⇒ (≠ e₁ ⨾ e₂)

    NORM-SEQ-DEFL :
      x ∉ fv eu
      ─────────
      eu ⨾ (∃ x ⇒ e) ≠—→≠ ∃ x ⇒ (eu ⨾ e)

    NORM-DEFR :
      y ∉ fv (v , e₂)
      ───────────────
      v ＝ (∃ y ⇒ e₁) ⨾ e₂ ≠—→≠ ∃ y ⇒ v ＝ e₁ ⨾ e₂

    NORM-SEQR :
      v ＝ (eu ⨾ e₁) ⨾ e₂ ≠—→≠ eu ⨾ v ＝ e₁ ⨾ e₂

    -- one

    ONE-FAIL :
      one⦅ fail ⦆ ≠—→≠ fail

    ONE-CHOICE :
      one⦅ ` v₁ ∣ e₂ ⦆ ≠—→≠ ` v₁

    ONE-VALUE :
      one⦅ ` v ⦆ ≠—→≠ ` v

    -- all

    ALL-FAIL :
      all⦅ fail ⦆ ≠—→≠ `⟨⟩

    ALL-CHOICE : ⦃ _ : ≠[] vs ⦄ →
      all⦅ ∣⁺ vs ⦆ ≠—→≠ `⟨ vs ⟩

    -- choice

    CHOOSE : ⦃ _ : cx ≠∙ ⦄ →
      -- cx [ e₁ ∣ e₂ ] ≠—→≠ cx [ e₁ ] ∣ cx [ e₂ ]
      e ≡ cx [ e₁ ∣ e₂ ]
      ────────────────────────────
      e ≠—→≠ cx [ e₁ ] ∣ cx [ e₂ ]

  data _—→_ : Rel₀ ＝Expr where

    ≠_ :
      e ≠—→≠ e′
      ──────────
      ≠ e —→ ≠ e′

    U-FAIL : ⦃ _ : isHead hnf₁ ⦄ ⦃ _ : isHead hnf₂ ⦄
      → hnf₁ —↛⟨U-SCALAR⟩ hnf₂
      → hnf₁ —↛⟨U-TUP⟩ hnf₂
        ──────────────────────
        hnf₁ ＝` hnf₂ —→ ≠ fail

confluence : WellFounded _≠—→≠_
confluence = acc ∘ _←—_
  where
    _←—_ : ∀ e e′ → e′ ≠—→≠ e → Acc _≠—→≠_ e′
    (e ←— e′) p = {!!}

confluence′ : WellFounded _—→_
confluence′ = acc ∘ _←—_
  where
    _←—_ : ∀ e e′ → e′ —→ e → Acc _—→_ e′
    ((≠ e) ←— (≠ e′)) (≠ p) = {!!}
    (.(≠ fail) ←— .(_ ＝` _)) (U-FAIL x x₁) = {!!}

-- confluence : WellFounded _—→_
-- confluence = acc ∘ _←—_
--   where
--     absurd₁ : ∀ {y v v′} → ¬ (y —→ v ＝ `𝕧 v′)
--     absurd₁ (NORM-EQ-SWAP ⦃ () ⦄)

--     _←—_ : ∀ e e′ → e′ —→ e → Acc _—→_ e′
--     ((.(𝕧 _) ＝ .(` v′)) ←— (v′ ＝ .(`𝕧 _))) NORM-EQ-SWAP
--       = acc λ y y→ → ⊥-elim $ absurd₁ y→
--     ((v ＝ e) ←— (≠ e′)) ()
--     ((≠ .fail) ←— (v ＝ .(` _))) (U-FAIL x x₁) = acc λ _ y→ → {!(_ ←— _)!}
--     ((≠ e)   ←— (≠ e′))    p = {!p!}

-- _—→?_ : Decidable² _—→_
-- e —→? e′ = {!e e′!}

freeIn : ⦃ _ : HasVars A ⦄ → A → Var
freeIn a = "$" Str.++ Str.concat (fv a)

`if_then_else_ : Op₃ Expr
`if e₁ then e₂ else e₃ =
  let y = freeIn (e₁ , e₂ , e₃)
      x = freeIn y
  in
  ∃ y ⇒ 𝕧 y ＝ one⦅ ≠ e₁ ⨾ ` (ƛ x ⇒ e₂) ∣ (` (ƛ x ⇒ e₃)) ⦆
      ⨾ (𝕧 y) · ⟨⟩

pattern for_ e = all⦅ e ⦆

for_do⦅_⦆ : Op₂ Expr
for e₁ do⦅ e₂ ⦆ =
  let y = freeIn (e₁ , e₂)
      x = freeIn y
      z = freeIn x
  in
  ∃ y ⇒ 𝕧 y ＝ all⦅ ≠ e₁ ⨾ ` (ƛ x ⇒ e₂) ⦆
      ⨾ ( (♯ ♯map) · ⟨ ⟦ (ƛ z ⇒ 𝕧 z · ⟨⟩) , 𝕧 y ⟧ ⟩)

open ReflexiveTransitiveClosure _—→_

-- _ : 𝕜2 ＝` 𝕜3 —→ ≠ fail
-- _ = U-FAIL (λ where (_ , x , y) → ?) proj₁

private module _ {e} where
  _ : ≠ (⟨ ⟦ 𝕜2 , 𝕜3 ⟧ ⟩ ＝` ⟨ ⟦ 𝕜2 , 𝕜3 ⟧ ⟩ ⨾ e) —↠ ≠ e
  _ =
    begin
      ≠ (⟨ ⟦ 𝕜2 , 𝕜3 ⟧ ⟩ ＝` ⟨ ⟦ 𝕜2 , 𝕜3 ⟧ ⟩ ⨾ e)
    —→⟨ ≠ U-TUP ⟩
      ≠ (𝕜2 ＝` 𝕜2 ⨾ 𝕜3 ＝` 𝕜3 ⨾ e)
    —→⟨ ≠ U-SCALAR ⟩
      ≠ (𝕜3 ＝` 𝕜3 ⨾ e)
    —→⟨ ≠ U-SCALAR ⟩
      ≠ e
    ∎

pattern _`+_ x y = ♯ add · ⟨ x ∷ y ∷ [] ⟩

-- private module _ {x y z : Value} where
--   _ : ≠ (x `+ (? ∣ ?)) —↠ ≠ ((x `+ y) ∣ (x `+ z))
--   _ =
--     begin
--       ≠ (x + (y ∣ z))
--     —→⟨ ? ⟩
--       ≠ (x + y ∣ x + z)
--     ∎

progress : ∀ e → Dec $ ∃ (e ≠—→≠_)
progress (` x) = no λ where (e′ , CHOOSE eq) → {!!}
progress (eu ⨾ e) = {!!}
progress (∃ x ⇒ e) = {!!}
progress (fail) = no λ where (_ , e→) → {!e→!}
progress (e ∣ e′) = {!!}
progress (v · v′) = {!!}
progress (one⦅ e ⦆) = {!!}
progress (for e) = {!!}

progress＝ : ∀ eu → Dec $ ∃ (eu —→_)
progress＝ (v ＝` v′)
  with isHead? v
... | no ¬hdv = no λ where (_ , U-FAIL ⦃ hdv ⦄ _ _) → ¬hdv hdv
... | yes hdv
  with isHead? v′
... | no ¬hdv′ = no λ where (_ , U-FAIL ⦃ _ ⦄ ⦃ hdv′ ⦄ _ _) → ¬hdv′ hdv′
... | yes hdv′
  with v —↛⟨U-SCALAR⟩? v′
... | no ¬p = no λ where (_ , U-FAIL p _) → ¬p p
... | yes ¬U-SCALAR
  with v —↛⟨U-TUP⟩? v′
... | no ¬p = no λ where (_ , U-FAIL _ p) → ¬p p
... | yes ¬U-TUP
    = yes (≠ fail , U-FAIL ⦃ hdv ⦄ ⦃ hdv′ ⦄ ¬U-SCALAR ¬U-TUP)
progress＝ (v ＝ (x ⨾ e)) = no λ ()
progress＝ (v ＝ (∃ x ⇒ e)) = no λ ()
progress＝ (v ＝ fail) =  no λ ()
progress＝ (v ＝ (e ∣ e₁)) = no λ ()
progress＝ (v ＝ (x · x₁)) = no λ ()
progress＝ (v ＝ one⦅ e ⦆) = no λ ()
progress＝ (v ＝ (for e)) = no λ ()
progress＝ (≠ e) with progress e
... | yes (_ , e→) = yes (-, ≠ e→)
... | no ¬p = no λ where (_ , ≠ e→) → ¬p (-, e→)
