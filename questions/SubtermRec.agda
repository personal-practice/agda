module SubtermRec where

open import Induction using (Recursor)
open import Data.List.Membership.Propositional.Properties
open import Data.List.Relation.Binary.Subset.Propositional.Properties

open import Prelude.Init
open import Prelude.Semigroup
open import Prelude.Applicative
open import Prelude.Nary
open import Prelude.Bifunctor
open import Prelude.Lists

{-
-- Simple arithmetic expressions.
data Exp : Set where
  ` : ℕ → Exp
  _`+_ : Exp → Exp → Exp

ex : Exp
ex = ` 5 `+ (` 10 `+ ` 0)

subterms subterms⁺ : Exp → List Exp
subterms⁺ x = x ∷ subterms x

subterms (` _)     = []
subterms (e `+ e′) = subterms⁺ e ++ subterms⁺ e′

collect : (e : Exp) → subterms e ↦ X → List X
collect (` _)    _ = []
collect (l `+ r) f = collect l (f ∘ ∈-++⁺ˡ ∘ there)
                  ++ collect r (f ∘ ∈-++⁺ʳ (subterms⁺ l) ∘ there)

mid : (e : Exp) → subterms e ↦ ℕ
mid (l `+ r) x∈
  with ∈-++⁻ (subterms⁺ l) x∈
... | inj₁ (here refl) = sum $ collect l (mid l)
... | inj₁ (there x∈ˡ) = mid l x∈ˡ
... | inj₂ (here refl) = sum $ collect r (mid r)
... | inj₂ (there x∈ʳ) = mid r x∈ʳ

level : (e : Exp) → subterms e ↦ ℕ
level e = go e 0
  where
    go : (e : Exp) → ℕ → subterms e ↦ ℕ
    go (l `+ r) lvl x∈
      with lvl′ ← suc lvl
      with ∈-++⁻ (subterms⁺ l) x∈
    ... | inj₁ (here refl) = lvl′
    ... | inj₁ (there x∈ˡ) = go l lvl′ x∈ˡ
    ... | inj₂ (here refl) = lvl′
    ... | inj₂ (there x∈ʳ) = go r lvl′ x∈ʳ
-}

{-
-- Expressions containing lists of expressions.
data Exp′ : Set where
  ` : ℕ → Exp′
  ∑_ : List Exp′ → Exp′

ex′ : Exp′
ex′ = ∑ ⟦ ` 5 , ∑ [ ` 10 ] ⟧

𝔼 : Set
𝔼 = Exp′ ⊎ List Exp′

subterms′ subterms⁺′ : Exp′ → List Exp′
subtermss′ : List Exp′ → List Exp′

subterms⁺′ x = x ∷ subterms′ x

subterms′ (` _)  = []
subterms′ (∑ es) = subtermss′ es

subtermss′ []       = []
subtermss′ (e ∷ es) = subterms⁺′ e ++ subtermss′ es


collect′ : (e : Exp′) → subterms′ e ↦ X → List X
collects′ : (es : List Exp′) → subtermss′ es ↦ X → List X

collect′ (` x)  = const []
collect′ (∑ es) = collects′ es

collects′ []       _ = []
collects′ (e ∷ es) f = collect′ e (f ∘ ∈-++⁺ˡ ∘ there)
                    ++ collects′ es (λ x∈ → f (there (∈-++⁺ʳ (subterms′ e) x∈)))

mid′ : (e : Exp′) → subterms′ e ↦ ℕ
mids′ : (es : List Exp′) → subtermss′ es ↦ ℕ

mid′ (∑ es) = mids′ es

mids′ (e ∷ es) x∈
  with ∈-++⁻ (subterms⁺′ e) x∈
... | inj₁ (here refl) = sum $ collect′ e (mid′ e)
... | inj₁ (there x∈ˡ) = mid′ e x∈ˡ
... | inj₂ x∈ʳ         = mids′ es x∈ʳ

level′ : (e : Exp′) → subterms′ e ↦ ℕ
level′ e = go e 0
  where
    go : (e : Exp′) → ℕ → subterms′ e ↦ ℕ
    gos : (es : List Exp′) → ℕ → subtermss′ es ↦ ℕ

    go (∑ es) lvl = gos es (suc lvl)

    gos (e ∷ es) lvl x∈
      with ∈-++⁻ (subterms⁺′ e) x∈
    ... | inj₁ (here refl) = lvl
    ... | inj₁ (there x∈ˡ) = go e lvl x∈ˡ
    ... | inj₂ x∈ʳ         = gos es lvl x∈ʳ


_ : level′ ex′ (here refl) ≡ 1
_ = refl
_ : level′ ex′ (there (here refl)) ≡ 1
_ = refl
_ : level′ ex′ (there (there (here refl))) ≡ 2
_ = refl
-}

--

data Exp : Set where
  ` : ℕ → Exp
  ∑_ : List Exp → Exp


ex : Exp
ex = ∑ ⟦ ` 5 , ∑ [ ` 10 ] ⟧

𝔼 = Exp ⊎ List Exp

variable
  x y : Level
  X : Set x
  Y : Set y

  e  e′  : Exp
  es es′ : List Exp
  E  E′  : 𝔼


-- ** AGDA BUG ** Cannot use automatic lifting because termination starts failing all around...
record To𝔼 (A : Set) : Set where
  field
    to𝔼 : A → 𝔼
open To𝔼 {{...}} public

instance
  To𝔼₀ : To𝔼 𝔼
  To𝔼₀ .to𝔼 = λ x → x

  To𝔼₁ : To𝔼 Exp
  To𝔼₁ .to𝔼 = inj₁

  To𝔼₂  : To𝔼 (List Exp)
  To𝔼₂ .to𝔼 = inj₂

↑ : {{_ : To𝔼 X}} → (𝔼 → Y) → (X → Y)
↑ f x = f (to𝔼 x)

names : 𝔼 → List ℕ
names (inj₁ e) with e
... | ` x  = [ x ]
... | ∑ es = names (inj₂ es)
names (inj₂ [])       = []
names (inj₂ (e ∷ es)) = names (inj₁ e) ++ names (inj₂ es)

_ : names (inj₁ ex) ≡ ⟦ 5 , 10 ⟧
_ = refl

subterms : 𝔼 → List Exp
subterms (inj₁ e) with e
... | ` _  = []
... | ∑ es = subterms (inj₂ es)
subterms (inj₂ []) = []
subterms (inj₂ (e ∷ es)) = e ∷ subterms (inj₁ e) ++ subterms (inj₂ es)

_ : subterms (inj₁ ex) ≡ ⟦ ` 5 , ∑ [ ` 10 ] , ` 10 ⟧
_ = refl

--

Sechash : 𝔼 → Set
Sechash e = names e ↦ ⊤

names⊆₁ : ∀ e′ {e} → e ∈ subterms (inj₁ e′) → names (inj₁ e) ⊆ names (inj₁ e′)
names⊆₂ : ∀ es {e} → e ∈ subterms (inj₂ es) → names (inj₁ e) ⊆ names (inj₂ es)

names⊆₁ (∑ es) = names⊆₂ es

names⊆₂ (_ ∷ es) (here refl) = ∈-++⁺ˡ
names⊆₂ (e ∷ es) (there e∈)
  with ∈-++⁻ (subterms (inj₁ e)) e∈
... | inj₁ e∈ˡ = ∈-++⁺ˡ ∘ names⊆₁ e e∈ˡ
... | inj₂ e∈ʳ = ∈-++⁺ʳ _ ∘ names⊆₂ es e∈ʳ

names⊆ : e ∈ subterms E → ↑ names e ⊆ names E
names⊆ {E = inj₁ e}  = names⊆₁ e
names⊆ {E = inj₂ es} = names⊆₂ es

--

data _≺_ : Rel 𝔼 0ℓ where

  instance
    [L→R] : inj₁ e ≺ inj₂ (e ∷ es)

    [R→L] : inj₂ es ≺ inj₁ (∑ es)

    [R→R] : inj₂ es ≺ inj₂ (e ∷ es)

≺-wf : WellFounded _≺_
≺-wf = acc ∘ _≻_
  where
    _≻_ : ∀ e e′ → e′ ≺ e → Acc _≺_ e′
    (.(inj₂ (_ ∷ _)) ≻ .(inj₁ _)) [L→R] = acc (inj₁ _ ≻_)
    (.(inj₁ (∑ _))   ≻ .(inj₂ _)) [R→L] = acc (inj₂ _ ≻_)
    (.(inj₂ (_ ∷ _)) ≻ .(inj₂ _)) [R→R] = acc (inj₂ _ ≻_)

≺-rec : Recursor (WF.WfRec _≺_)
≺-rec = WF.All.wfRec ≺-wf 0ℓ

--

State : 𝔼 → Set
State e = ℕ × Sechash e

Return : 𝔼 → Set
Return e = subterms e ↦ ℕ

nextState : E ≺ E′ → State E′ → State E
nextState [L→R] (lvl , sh) = (lvl , sh ∘ ∈-++⁺ˡ)
nextState [R→L] (lvl , sh) = (suc lvl , sh)
nextState [R→R] (lvl , sh) = (lvl , sh ∘ ∈-++⁺ʳ _)

level : ∀ e → Sechash e → Return e
level e sechash = (≺-rec _ go) e (0 , sechash)
  where
    go : ∀ e → (∀ e′ → e′ ≺ e → State e′ → Return e′) → State e → Return e
    go (inj₁ (∑ es))   f st x∈
      = f (inj₂ es) it (nextState ([R→L] {es}) st) x∈
    go (inj₂ (e ∷ es)) f st x∈
      with ∈-++⁻ (e ∷ subterms (inj₁ e)) x∈
    ... | inj₁ (there x∈ˡ) = f (inj₁ e)  it (nextState ([L→R] {e}{es}) st) x∈ˡ
    ... | inj₂ x∈ʳ         = f (inj₂ es) it (nextState ([R→R] {es}{e}) st) x∈ʳ
    ... | inj₁ (here refl)
      with e
    ... | ` x = proj₁ st
      where
        t : ⊤
        t = proj₂ st (names⊆ {E = inj₂ (` x ∷ es)} x∈ (here refl))
    ... | e'   = proj₁ st


{-

Termination : 𝔼 → Set
Termination e = Acc _≺_ e

Rec : ∀ X → {{_ : To𝔼 X}} → Set
Rec X = (e : X) → ↑ Termination e → ↑ State e  → ↑ subterms e  ↦ ↑ Return e

level : ∀ e → Sechash e → subterms e ↦ Return e
level e₀ sechash = go e₀ (≺-wf e₀) (0 , sechash)
  where
    go₁ : Rec Exp
    go₂ : Rec (List Exp)

    go₁ (∑ es)   (acc a) st = go₂ es (a _ it) (nextState ([R→L] {es}) st)
    go₂ (e ∷ es) (acc a) st x∈
      with ∈-++⁻ (e ∷ subterms (inj₁ e)) x∈
    ... | inj₁ (there x∈ˡ) = go₁ e  (a _ it) (nextState ([L→R] {e}{es}) st) x∈ˡ
    ... | inj₂ x∈ʳ         = go₂ es (a _ it) (nextState ([R→R] {es}{e}) st) x∈ʳ
    ... | inj₁ (here refl)
      with e
    ... | ` x = getReturn {E = inj₂ (` x ∷ es)} st
      where
        t : ⊤
        t = proj₂ st (names⊆ {E = inj₂ (` x ∷ es)} x∈ (here refl))
    ... | e'   = getReturn {E = inj₂ (e' ∷ es)} st

    go : Rec 𝔼
    go (inj₁ e)  = go₁ e
    go (inj₂ es) = go₂ es
-}

    -- ** NB: termination fails, unless we unpack the recursion in two mutually defined recursors
    {-
    go : (e : 𝔼) → ℕ → subterms e ↦ ℕ
    go e₀ lvl x∈
      with e₀ | lvl | x∈
    ... | inj₁ (∑ es)   | lvl′ | x∈′ = go (inj₂ es) (suc lvl′) x∈′
    ... | inj₂ (e ∷ es) | lvl′ | x∈′
      with ∈-++⁻ (e ∷ subterms (inj₁ e)) x∈′
    ... | inj₁ (here refl) = lvl
    ... | inj₁ (there x∈ˡ) = go (inj₁ e) lvl′ x∈ˡ
    ... | inj₂ x∈ʳ         = go (inj₂ es) lvl′ x∈ʳ
    -}

    -- ** Options 1: Immediately use the sub-recursors (need to change the use site)
    {-
    go : (e : Exp) → ℕ → subterms (inj₁ e) ↦ ℕ
    gos : (es : List Exp) → ℕ → subterms (inj₂ es) ↦ ℕ

    go (∑ es) lvl = gos es (suc lvl)

    gos (e ∷ es) lvl (here refl) = lvl
    gos (e ∷ es) lvl (there x∈)
      with ∈-++⁻ (subterms (inj₁ e)) x∈
    ... | inj₁ x∈ˡ = go e lvl x∈ˡ
    ... | inj₂ x∈ʳ = gos es lvl x∈ʳ

    -- ** Options 2: Wrap the mutual calls around a single function
    see code
    -}

module _ where

  sechash : ↑ Sechash ex
  sechash = λ{ (here refl) → tt; (there (here refl)) → tt}

  _ : level (inj₁ ex) sechash (here refl) ≡ 1
  _ = refl
  _ : level (inj₁ ex) sechash (there (here refl)) ≡ 1
  _ = refl
  _ : level (inj₁ ex) sechash (there (there (here refl))) ≡ 2
  _ = refl


{-
∣_∣ : 𝔼 → ℕ
∣ inj₁ (` _)  ∣ = 0
∣ inj₁ (∑ es) ∣ = 0
∣ inj₂ [] ∣ = 0

instance
  Measurable-𝔼 : Measurable 𝔼
  Measurable-𝔼 .∣_∣
-}

{-
_≺_ : Rel 𝔼 0ℓ
x ≺ y = x ∈ subterms y

≺-wf : WellFounded _≺_
≺-wf = acc ∘ _≻_
  where
    _≻_ : ∀ e e′ → e′ ≺ e → Acc _≺_ e′
    (inj₁ (∑ es) ≻ .(inj₂ es)) (here refl) = acc (inj₂ es ≻_)
    (inj₁ (∑ (e ∷ es)) ≻ x) (there x∈)
      with ∈-++⁻ (go (inj₁ e)) x∈
    ... | inj₁ (here refl) = {!!}
    ... | inj₁ (there x∈ˡ) = (inj₁ e ≻ x) x∈ˡ
    ... | inj₂ x∈ʳ = {!!}
    -- (inj₂ es ≻ x) x∈

    -- (inj₂ es ≻ x) x∈ = (inj₁ (∑ es) ≻ x) {!!}

    (inj₂ (e ∷ es) ≻ x) x∈
      with ∈-++⁻ (go (inj₁ e)) x∈
    ... | inj₁ (here px) = {!!}
    ... | inj₁ (there x∈ˡ) = {!!} -- (inj₁ e ≻ x) x∈ˡ
    ... | inj₂ x∈ʳ = {!!}
-}
