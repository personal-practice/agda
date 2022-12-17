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
  data Value : Type
  Values = List Value
  data Expr : Type
  ≠_ : Pred₀ Expr

  ≠Expr = ∃ ≠_

  data Value where
    𝕧 : Var → Value
    𝕜 : ℕ → Value
    ♯ : Primop → Value
    ⟨_⟩ : Values → Value
    `ƛ_⇒_ : Var → ≠Expr → Value

  data Expr where
    `_ : Value → Expr
    _`⨾_ : Expr → ≠Expr → Expr
    `∃_⇒_ : Var → ≠Expr → Expr
    fail : Expr
    _`∣_ : ≠Expr → ≠Expr → Expr
    _·_ : Value → Value → Expr
    `one⦅_⦆ `all⦅_⦆ : ≠Expr → Expr
    _`＝_ : Value → ≠Expr → Expr

  ≠_ = λ where
    (_ `＝ _) → ⊥
    -- (e `⨾ _) → ≠ e
    _ → ⊤

infixr 2 `∃_⇒_ ∃_⇒_ `ƛ_⇒_ ƛ_⇒_
infixr 3 _`∣_ _∣_
infixr 4 _`⨾_ _⨾_
infix  5 _`＝_ _＝_ _＝`_

ƛ_⇒_ : Var → (e : Expr) ⦃ _ : ≠ e ⦄ → Value
ƛ x ⇒ e = `ƛ x ⇒ (e , it)

_⨾_ : (e e′ : Expr) ⦃ _ : ≠ e′ ⦄ → Expr
e ⨾ e′ = e `⨾ (e′ , it)

∃_⇒_ : Var → (e : Expr) ⦃ _ : ≠ e ⦄ → Expr
∃ x ⇒ e = `∃ x ⇒ (e , it)

_∣_ : (e e′ : Expr) ⦃ _ : ≠ e ⦄ ⦃ _ : ≠ e′ ⦄ → Expr
e ∣ e′ = (e , it) `∣ (e′ , it)

one⦅_⦆ all⦅_⦆ : (e : Expr) ⦃ _ : ≠ e ⦄ → Expr
one⦅ e ⦆ = `one⦅ e , it ⦆
all⦅ e ⦆ = `all⦅ e , it ⦆

_＝_ : Value → (e : Expr) ⦃ _ : ≠ e ⦄ → Expr
v ＝ e = v `＝ (e , it)

_＝`_ : Value → Value → Expr
v ＝` v′ = v `＝ (` v′ , it)

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
  (`ƛ _ ⇒ _) → ⊤
  _ → ⊥
-- isHead = isHeap Unary.∪ isConstant
isHead = λ where
  ⟨ _ ⟩ → ⊤
  (`ƛ _ ⇒ _) → ⊤
  (𝕜 _) → ⊤
  _ → ⊥

_ : Expr
_ = ∃ "x" ⇒ (∃ "y" ⇒ `⟨ ⟦ 𝕜2    , 𝕧 "y" ⟧ ⟩) ⨾
            (∃ "z" ⇒ `⟨ ⟦ 𝕧 "y" , 𝕜3    ⟧ ⟩) ⨾
            `𝕧 "x"

-- ** helpers

private variable
  e e′ e₁ e₂ eu : Expr
  v v₁ v₂ v₁′ v₂′ : Value
  vs : Values
  s s′ : Value
  hnf hnf₁ hnf₂ : Value
  x y : Var
  k₁ k₂ n : ℕ

eu≠_ : Pred₀ Expr
eu≠_ = λ where
  (𝕧 _ `＝ (` _ , _)) → ⊥
  _ → ⊤

≠[] : Pred₀ (List A)
≠[] = λ where
  [] → ⊥
  (_ ∷ _) → ⊤

mutual
  ∣⁺_ : (vs : Values) ⦃ _ : ≠[] vs ⦄ → Expr
  ∣⁺_ = λ where
    (v ∷ []) → ` v
    (v ∷ vs@(_ ∷ _)) → ` v ∣ ∣⁺ vs

  instance
    ∣⁺-≠[] : ⦃ _ : ≠[] vs ⦄ → ≠ (∣⁺ vs)
    ∣⁺-≠[] {_ ∷ []} = tt
    ∣⁺-≠[] {_ ∷ _ ∷ _} = tt

mutual
  enum-∣ : Var → (vs : Values) ⦃ _ : ≠[] vs ⦄ → Expr
  enum-∣ x vs = go 0 vs
    where mutual
      go : ℕ → (vs : Values) ⦃ _ : ≠[] vs ⦄ → Expr
      go i = let x＝i = 𝕧 x ＝` 𝕜 i in λ where
        (v ∷ []) → x＝i ⨾ ` v
        (v ∷ vs@(_ ∷ _)) → x＝i ⨾ ` v ∣ go (suc i) vs

      instance
        go-≠[] : ∀ {vs : Values} ⦃ _ : ≠[] vs ⦄ → ≠ (go n vs)
        go-≠[] {vs = _ ∷ []}    = tt
        go-≠[] {vs = _ ∷ _ ∷ _} = tt

  instance
    enum-∣-≠[] : ⦃ _ : ≠[] vs ⦄ → ≠ (enum-∣ x vs)
    enum-∣-≠[] {_ ∷ []} = tt
    enum-∣-≠[] {_ ∷ _ ∷ _} = tt

-- ** free variables
record HasVars (A : Type) : Type where
  field fv : A → List Var
  fvs : List A → List Var
  fvs = concatMap fv
open HasVars ⦃...⦄ public

mutual instance
  hv : HasVars Var
  hv .fv x = x ∷ []

  hv× : ⦃ HasVars A ⦄ → ⦃ ∀ {a} → HasVars (P a) ⦄ → HasVars (Σ A P)
  hv× .fv (a , b) = fv a ++ fv b

  hv≠ : HasVars (≠ e)
  hv≠ .fv _ = []

  {-# TERMINATING #-}
  hve : HasVars Expr
  hve .fv = λ where
    (` _) → []
    (e `⨾ e′) → fv (e , e′)
    (`∃ x ⇒ e) → filter (¬? ∘ (_≟ x)) (fv e)
    fail → []
    (e `∣ e′) → fv (e , e′)
    (v · v′) → fv (v , v′)
    `one⦅ e ⦆ → fv e
    `all⦅ e ⦆ → fv e
    (v `＝ e) → fv (v , e)

  hvv : HasVars Value
  hvv .fv = λ where
    (𝕧 x) → x ∷ []
    (𝕜 _) → []
    (♯ _) → []
    ⟨ vs ⟩ → fvs vs
    (`ƛ x ⇒ e) → filter (¬? ∘ (_≟ x)) (fv e)

-- ** choices
∣-free : Pred₀ Expr
∣-free = λ where
  (_ `∣ _) → ⊥
  (e `⨾ (e′ , _)) → ∣-free e × ∣-free e′
  (`∃ _ ⇒ (e , _)) → ∣-free e
  `one⦅ e , _ ⦆ → ∣-free e
  `all⦅ e , _ ⦆ → ∣-free e
  (_ `＝ (e , _)) → ∣-free e
  _ → ⊤

data EP : Type where
  ∗ ？ : EP
variable ep : EP

⟦_⟧ᵉᵖ : EP → Pred₀ Expr
⟦_⟧ᵉᵖ = λ where
  ∗ → const ⊤
  ？ → ≠_

mutual
  data CX : EP → Type₁ where
    ∙ : CX ∗
    _＝∙_ : Value → ≠CX ep → CX ？
    _∙⨾_ : CX ep → ≠Expr → CX ep
    _⨾∙_ : (ce : Expr) ⦃ _ : ∣-free ce ⦄ → ≠→∙CX ep → CX ep
    ∃_⇒∙_ : Var → ≠CX ep → CX ？

  ≠ᵉᵖ_ ≠→∙_ : Pred₀ (CX ep)
  ≠ᵉᵖ_ = λ where
    (_ ＝∙ _) → ⊥
    _ → ⊤
  ≠→∙_ {ep = ep} = λ where
    (_ ＝∙ _) → ⊥
    ∙ → ep ≡ ？
    _ → ⊤

  ≠CX ≠→∙CX : EP → Type₁
  ≠CX ep = Σ (CX ep) ≠ᵉᵖ_
  ≠→∙CX ep = Σ (CX ep) ≠→∙_

variable cx cx′ : CX ep

≠∙_ : Pred₀ (CX ep)
≠∙_ = λ where
  ∙ → ⊥
  _ → ⊤

weakenCX : ⟦ ？ ⟧ᵉᵖ e → ⟦ ep ⟧ᵉᵖ e
weakenCX {ep = ∗} = const tt
weakenCX {ep = ？} = id

mutual
  _[_] : (cx : CX ep) → (e : Expr) ⦃ _ : ⟦ ep ⟧ᵉᵖ e ⦄ → Expr
  _[_] ∙ e = e
  _[_] (_＝∙_ {ep} x (cx , ≠cx)) e
    = x `＝ (cx [ e ] , cx-≠ ⦃ ≠cx ⦄)
    where instance _ = weakenCX {ep = ep} it
  _[_] (cx ∙⨾ e′) e
      = cx [ e ] `⨾ e′
  _[_] (ce ⨾∙ (cx , ≠cx)) e
    = ce `⨾ cx [ e ] , cx≠ ≠cx
  _[_] (∃_⇒∙_ {ep} x (cx , ≠cx)) e
    = `∃ x ⇒ (cx [ e ] , cx-≠ ⦃ ≠cx ⦄)
    where instance _ = weakenCX {ep = ep} it

  cx≠′ : {cx : CX ep} ⦃ _ : ⟦ ep ⟧ᵉᵖ e ⦄ ⦃ _ : ≠ᵉᵖ cx ⦄
       → (≠∙ cx) ⊎ (≠ e)
       → ≠ (cx [ e ])
  cx≠′ {cx = ∙} (inj₂ ≠e) = ≠e
  cx≠′ {cx = cx ∙⨾ x} p = tt
  cx≠′ {cx = ce ⨾∙ x} p = tt
  cx≠′ {cx = ∃ x ⇒∙ x₁} p = tt

  cx≠ : {cx : CX ep} ⦃ _ : ⟦ ep ⟧ᵉᵖ e ⦄ → ≠→∙ cx → ≠ (cx [ e ])
  cx≠ {cx = cx ∙⨾ x} p = tt
  cx≠ {cx = ce ⨾∙ x} p = tt
  cx≠ {cx = ∃ x ⇒∙ x₁} p = tt

  cx-≠ : {cx : CX ep} ⦃ _ : ≠ᵉᵖ cx ⦄
        → ⦃ _ : ⟦ ep ⟧ᵉᵖ e ⦄ ⦃ _ : ≠ e ⦄
        → ≠ (cx [ e ])
  cx-≠ {cx = cx} ⦃ _ ⦄ ⦃ _ ⦄ ⦃ ≠e ⦄ with cx
  ... | ∙        = ≠e
  ... | _   ∙⨾ _ = tt
  ... | _   ⨾∙ _ = tt
  ... | ∃ _ ⇒∙ _ = tt

-- ** Unification rewrite rules

infix 0 _—→_
data _—→_ : Rel Expr _ where

  U-SCALAR : ⦃ _ : ≠ e ⦄ ⦃ _ : isConstant s ⦄ →
    s ＝` s ⨾ e —→ e

  U-TUP : ⦃ _ : ≠ e ⦄ →
    ⟨ ⟦ v₁ , v₂ ⟧ ⟩ ＝` ⟨ ⟦ v₁′ , v₂′ ⟧ ⟩ ⨾ e —→ v₁ ＝` v₁′ ⨾ v₂ ＝` v₂′ ⨾ e

  U-FAIL : ⦃ _ : isHead hnf₁ ⦄ ⦃ _ : isHead hnf₂ ⦄ →
    ∙ ¬ (∃ λ s → (hnf₁ ≡ 𝕜 s) × (hnf₂ ≡ 𝕜 s)) -- no U-SCALAR match
    ∙ ¬ (isTup hnf₁ × isTup hnf₂) -- no U-TUP match
      ─────────────────────
      hnf₁ ＝` hnf₂ —→ fail

  -- Application: 𝓐

  APP-BETA : ⦃ _ : ≠ e ⦄ →
    x ∉ fv v
    ────────
    (ƛ x ⇒ e) · v —→ ∃ x ⇒ 𝕧 x ＝` v ⨾ e

  APP-TUP₀ :
    ⟨⟩ · v —→ fail

  APP-TUP : ⦃ _ : ≠[] vs ⦄ →
    x ∉ fv v
    ────────
    ⟨ vs ⟩ · v —→ ∃ x ⇒ 𝕧 x ＝` v ⨾ enum-∣ x vs

  APP-ADD :
    (♯ add) · ⟨ ⟦ 𝕜 k₁ , 𝕜 k₂ ⟧ ⟩ —→ `𝕜 (k₁ + k₂)

  APP-GT : {auto∶ k₁ > k₂} →
    (♯ gt) · ⟨ ⟦ 𝕜 k₁ , 𝕜 k₂ ⟧ ⟩ —→ `𝕜 k₁

  APP-GT-FAIL : {auto∶ k₁ ≤ k₂} →
    (♯ gt) · ⟨ ⟦ 𝕜 k₁ , 𝕜 k₂ ⟧ ⟩ —→ fail

  -- Normalization: 𝓝

  NORM-VAL : ⦃ _ : ≠ e ⦄ →
    ` v ⨾ e —→ e

  NORM-SEQ-ASSOC : ⦃ _ : ≠ e₁ ⦄ ⦃ _ : ≠ e₂ ⦄ →
    (eu ⨾ e₁) ⨾ e₂ —→ eu ⨾ (e₁ ⨾ e₂)

  NORM-SEQ-SWAP₁ : ⦃ _ : ≠ e ⦄ ⦃ _ : eu≠ eu ⦄ →
    eu ⨾ (𝕧 x ＝` v ⨾ e) —→ 𝕧 x ＝` v ⨾ (eu ⨾ e)

  -- NORM-SEQ-SWAP₂ : ⦃ _ : ≠ e ⦄ ⦃ _ : eu≠ eu ⦄ →
  --   eu ⨾ (𝕧 x ＝` s ⨾ e) —→ 𝕧 x ＝` s ⨾ (eu ⨾ e)

  NORM-EQ-SWAP : ⦃ _ : isHead hnf ⦄ →
    hnf ＝` 𝕧 x —→ 𝕧 x ＝` hnf

  NORM-SEQ-DEFR : ⦃ _ : ≠ e₁ ⦄ ⦃ _ : ≠ e₂ ⦄ →
    x ∉ fv e₂
    ─────────
    (∃ x ⇒ e₁) ⨾ e₂ —→ ∃ x ⇒ (e₁ ⨾ e₂)

  NORM-SEQ-DEFL : ⦃ _ : ≠ e ⦄ →
    x ∉ fv eu
    ─────────
    eu ⨾ (∃ x ⇒ e) —→ ∃ x ⇒ (eu ⨾ e)

  NORM-DEFR : ⦃ _ : ≠ e₁ ⦄ ⦃ _ : ≠ e₂ ⦄ →
    y ∉ fv (v , e₂)
    ───────────────
    v ＝ (∃ y ⇒ e₁) ⨾ e₂ —→ ∃ y ⇒ v ＝ e₁ ⨾ e₂

  NORM-SEQR : ⦃ _ : ≠ e₁ ⦄ ⦃ _ : ≠ e₂ ⦄ →
    v ＝ (eu ⨾ e₁) ⨾ e₂ —→ eu ⨾ v ＝ e₁ ⨾ e₂

  -- one

  ONE-FAIL :
    one⦅ fail ⦆ —→ fail

  ONE-CHOICE : ⦃ _ : ≠ e₂ ⦄ →
    one⦅ ` v₁ ∣ e₂ ⦆ —→ ` v₁

  ONE-VALUE :
    one⦅ ` v ⦆ —→ ` v

  -- all

  ALL-FAIL :
    all⦅ fail ⦆ —→ `⟨⟩

  ALL-CHOICE : ⦃ _ : ≠[] vs ⦄ →
    all⦅ ∣⁺ vs ⦆ —→ `⟨ vs ⟩

  -- choice

  CHOOSE : {cx : CX ep} ⦃ _ : ≠ᵉᵖ cx ⦄ ⦃ _ : ≠∙ cx ⦄ ⦃ _ : ≠ e₁ ⦄ ⦃ _ : ≠ e₂ ⦄
    ⦃ _ : ⟦ ep ⟧ᵉᵖ e₁ ⦄ ⦃ _ : ⟦ ep ⟧ᵉᵖ e₂ ⦄
    ⦃ _ : ⟦ ep ⟧ᵉᵖ (e₁ ∣ e₂) ⦄
    →
    -- let instance _ = cx-≠ {ep = ep} in
    let instance _ = cx≠ {ep = ep} {!!} in
    cx [ e₁ ∣ e₂ ] —→ _∣_ (cx [ e₁ ]) (cx [ e₂ ]) ⦃ cx-≠ ⦄



_—→?_ : Decidable² _—→_
e —→? e′ = {!e e′!}

freeIn : ⦃ _ : HasVars A ⦄ → A → Var
freeIn a = "$" Str.++ Str.concat (fv a)

`if_then_else_ : (e₁ e₂ e₃ : Expr) ⦃ _ : ≠ e₂ ⦄ ⦃ _ : ≠ e₃ ⦄ → Expr
`if e₁ then e₂ else e₃ =
  let y = freeIn (e₁ , e₂ , e₃)
      x = freeIn y
  in
  ∃ y ⇒ 𝕧 y ＝ one⦅ e₁ ⨾ ` (ƛ x ⇒ e₂) ∣ (` (ƛ x ⇒ e₃)) ⦆
      ⨾ (𝕧 y) · ⟨⟩

for_ : (e : Expr) ⦃ _ : ≠ e ⦄ → Expr
for e = all⦅ e ⦆

for_do⦅_⦆ : (e₁ e₂ : Expr) ⦃ _ : ≠ e₂ ⦄ → Expr
for e₁ do⦅ e₂ ⦆ =
  let y = freeIn (e₁ , e₂)
      x = freeIn y
      z = freeIn x
  in
  ∃ y ⇒ 𝕧 y ＝ all⦅ e₁ ⨾ ` (ƛ x ⇒ e₂) ⦆
      ⨾ ( (♯ ♯map) · ⟨ ⟦ (ƛ z ⇒ 𝕧 z · ⟨⟩) , 𝕧 y ⟧ ⟩)

open ReflexiveTransitiveClosure _—→_

_ : 𝕜2 ＝` 𝕜3 —→ fail
_ = U-FAIL (λ where (_ , refl , ())) proj₁

module _ ⦃ _ : ≠ e ⦄ where
  _ : ⟨ ⟦ 𝕜2 , 𝕜3 ⟧ ⟩ ＝` ⟨ ⟦ 𝕜2 , 𝕜3 ⟧ ⟩ ⨾ e —↠ e
  _ =
    begin
      ⟨ ⟦ 𝕜2 , 𝕜3 ⟧ ⟩ ＝` ⟨ ⟦ 𝕜2 , 𝕜3 ⟧ ⟩ ⨾ e
    —→⟨ U-TUP ⟩
      𝕜2 ＝` 𝕜2 ⨾ 𝕜3 ＝` 𝕜3 ⨾ e
    —→⟨ U-SCALAR ⟩
      𝕜3 ＝` 𝕜3 ⨾ e
    —→⟨ U-SCALAR ⟩
      e
    ∎
