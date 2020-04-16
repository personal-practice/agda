------------------------------------------------------------------------
-- Limitations of termination checking.
-- (e.g. when recursing through UTxO references)
------------------------------------------------------------------------
module UTxOTermination where

open import Function     using (_$_)
open import Data.Unit    using (⊤)
open import Data.Sum     using (inj₁; inj₂)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; proj₁; proj₂; map₁; map₂)
open import Data.Nat     using (ℕ)
  renaming (_≟_ to _≟ℕ_)
open import Data.List    using (List; []; _∷_; [_]; _++_; map; filter; concat)

open import Data.List.Properties using (≡-dec)

open import Data.List.Membership.Propositional             using (_∈_; mapWith∈; find)
open import Data.List.Membership.Propositional.Properties  using (∈-map⁻; ∈-++⁻; ∈-filter⁻)

open import Data.List.Relation.Unary.All as All            using (All; []; _∷_)
open import Data.List.Relation.Unary.Any                   using (Any; here; there)
open import Data.List.Relation.Unary.Unique.Propositional  using (Unique)
open import Data.List.Relation.Binary.Suffix.Heterogeneous using (here; there)
open import Data.List.Relation.Binary.Pointwise            using (_∷_; Pointwise-≡⇒≡)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong)
open import Relation.Binary                       using (Decidable)

open import Prelude.Lists

{- Generic well-founded recursion

open import Level
open import Induction
open import Induction.WellFounded
open import Relation.Binary

record WF (A : Set) : Set₁ where
  field
    _≺_      : Rel A 0ℓ
    ≺-wf     : WellFounded _≺_

open WF {{...}} public

≺-rec : ∀ {A : Set} {{_ : WF A}} → Recursor (WfRec _≺_)
≺-rec = All.wfRec ≺-wf 0ℓ

-}

HashId = ℕ
postulate _♯ : ∀ {A : Set} → A → HashId

record Node : Set where
  field
    id     : HashId
    inputs : List HashId

open Node public

open import Prelude.Set' {A = HashId} _≟ℕ_ hiding (_∈_)

DAG = List Node

---

open import Level
open import Induction
open import Induction.WellFounded
open import Relation.Binary

_≺_ : Rel DAG 0ℓ
g′ ≺ g = ∃[ x ] Suffix≡ (x ∷ g′) g

postulate
  ≺-trans : Transitive _≺_

≺-there : ∀ {g′ g x} → g′ ≺ g → g′ ≺ (x ∷ g)
≺-there = map₂ there

≺-wf : WellFounded _≺_
≺-wf g = acc $ go g
  where
    go : ∀ g g′ → g′ ≺ g → Acc _≺_ g′
    go (_ ∷ g) g′ (_ , here (refl ∷ eq)) = acc λ y y<g′ → go g y (subst (y ≺_) (Pointwise-≡⇒≡ eq) y<g′)
    go (_ ∷ g) g′ (_ , there g′<g)       = acc λ y y<g′ → go g y (≺-trans y<g′ (_ , g′<g))

---

free : DAG → List HashId
free []      = []
free (x ∷ g) = filter (_∉? inputs x) (free g) ++ [ id x ]

validRefs : Node → DAG → Set
validRefs x g
  = All (_∈ free g) (inputs x)
  × Unique (inputs x)

data VDAG : DAG → Set where
  ∙      : VDAG []
  _⊕_∶-_ : ∀ {g} → VDAG g → (x : Node) → validRefs x g → VDAG (x ∷ g)

_≺′_ : Rel (∃ VDAG) 0ℓ
(g , _) ≺′ (g′ , _) = g ≺ g′

_≺′⇒≺_ : ∀ vg → Acc _≺_ (proj₁ vg) → Acc _≺′_ vg
(g , _) ≺′⇒≺ acc w = acc λ{ (g′ , _) g′<g → (g′ , _) ≺′⇒≺ w g′ g′<g }

≺′-wf : WellFounded _≺′_
≺′-wf vg = vg ≺′⇒≺ ≺-wf (proj₁ vg)

≺′-rec = All.wfRec ≺′-wf 0ℓ

valid-suffix : ∀ {g g′}
  → VDAG g
  → Suffix≡ g′ g
  → VDAG g′
valid-suffix g             (here eq)   rewrite Pointwise-≡⇒≡ eq = g
valid-suffix (g ⊕ x ∶- vx) (there suf) = valid-suffix g suf

∈free⇒prevX : ∀ {i g}
  → i ∈ free g
  → ∃[ x′ ] ( (x′ ∈ g)
            × (id x′ ≡ i) )
∈free⇒prevX {i} {x ∷ g} i∈
  with ∈-++⁻ (filter (_∉? inputs x) (free g)) i∈
... | inj₁ i∈ˡ = {!!}
... | inj₂ i∈ʳ = {!!}

inputsₘ : ∃ VDAG → List HashId
inputsₘ ([]    , _) = []
inputsₘ (x ∷ _ , _) = inputs x

_≼_ : Rel DAG 0ℓ
_≼_ = Suffix≡

_≼′_ : Rel (∃ VDAG) 0ℓ
(g′ , _) ≼′ (g , _) = g′ ≼ g

postulate
  suffix-refl : ∀ {A : Set} → (xs : List A) → Suffix≡ xs xs

≺-transˡ : ∀ {x y z}
  → x ≼ y
  → y ≺ z
  → x ≺ z
≺-transˡ = {!!}

history : ∀ g → ∀ {i} → i ∈ inputsₘ g → List Node
history g = go _ (≺′-wf g)
  where
    go : ∀ g → Acc _≺′_ g → (∀ {i} → i ∈ inputsₘ g → List Node)
    go (.x ∷ g , vg₀@(vg ⊕ x ∶- (vrefs , _))) (acc a) {i} i∈
      with x′ , x∈′ , idx′≡ ← ∈free⇒prevX $ All.lookup vrefs i∈
      with g′ , suf         ← ∈⇒Suffix x∈′
         = x ∷ prevHistory
      where
        vg′ : VDAG (x′ ∷ g′)
        vg′ = valid-suffix vg suf

        suf′ : (x′ ∷ g′) ≼ g
        suf′ = suf

        g′<g : (x′ ∷ g′) ≺ (x ∷ g)
        g′<g = ≺-transˡ suf′ (x , suffix-refl (x ∷ g))

        prevHistory : List Node
        prevHistory = concat $ mapWith∈ (inputs x′) (go (_ , vg′) (a _ g′<g))

{-


history : ∀ vg → ∀ {i} → i ∈ inputsₘ vg → List Node
-- history    (_ , ∙)           ()
-- history vg@(_ , g ⊕ x ∶- vx) i∈ = x ∷ ≺′-rec _ go
history g = ≺′-rec _ (go g)
  where
    go : ∀ g g′
      → g′ ≺′ g
      →
      → (∀ y → y ≺′ vg′ → (∀ {i} → i ∈ inputsₘ y → List Node))
      → (∀ {i} → i ∈ inputsₘ vg′ → List Node)
    go vg vg′@(_ , _ ⊕ _ ∶- vx′) r i∈′
      with x′ , x∈′ , idx′≡ ← ∈free⇒prevX $ All.lookup (proj₁ vx′) i∈′
      with g′ , suf         ← ∈⇒Suffix x∈′
        = prevHistory
      where
        prevIs : List HashId
        prevIs = inputs x′

        vx′g : VDAG (x′ ∷ g′)
        vx′g = valid-suffix (proj₂ vg) suf

        -- vg′ = _ , vx′

        g′<g : vg′ ≺′ vg
        g′<g = ?

        prevHistory : List Node
        prevHistory = concat $ mapWith∈ prevIs ? -- (r vg′ g′<g)
-}

{-
history {x} (g ⊕ .x ∶- vx@(vrefs , uniq)) {i} i∈
  with i∈′              ← All.lookup vrefs i∈
  with x′ , x∈′ , idx′≡ ← ∈free⇒prevX i∈′
  with g′ , suf         ← ∈⇒Suffix x∈′
    = x ∷ prevHistory
  where
    prevIs : List HashId
    prevIs = inputs x′

    vx′ : VDAG (x′ ∷ g′)
    vx′ = valid-suffix g suf

    prevHistory : List Node
    prevHistory = concat $ mapWith∈ prevIs (history vx′)
-}
