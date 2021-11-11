{-# OPTIONS -v adhoc:100 #-}
open import Prelude.Init
open Meta
open import Prelude.Generics
open Debug ("adhoc" , 100)

postulate D : (A : Set) (B : A → Set) → Set
   -- ==> D′ : Set → Set → Set
D′ : Set → Set → Set
D′ a b = D a (const b)

postulate _⊗_ : ∀ {A : Set} {B : A → Set} (fst : A) (snd : B fst) → D A B
   -- ==> _⊗′_ : ∀ {A : Set} {B : Set} → A → B → D′ A B
_⊗′_ : ∀ {A : Set} {B : Set} → A → B → D′ A B
_⊗′_ = _⊗_

endsInSet : Type → Bool
endsInSet = {!!}

dropDependencies : Type → Type
dropDependencies = λ where
  (pi a b) → {!!}
  ty → ty

_ : dropDependencies (quoteTerm (ℕ × String)) ≡ quoteTerm (ℕ × String)
_ = refl

_ : dropDependencies (quoteTerm ((A : Set) (B : A → Set) → Set)) ≡ quoteTerm (Set → Set → Set)
_ = refl

macro
  deriveNonDependent : Hole → TC ⊤
  deriveNonDependent h = {!!}

⌞_⌟ : (∀ {A : Set} {B : A → Set} {C : (a : A) → B a → Set} → (a : A) → (b : B a) → C a b)
    → (∀ {A B C : Set} → A → B → C)
⌞ _⊕_ ⌟ = _⊕_

_,,_ : ∀ {A B : Set} → A → B → A × B
_,,_ = {!⌞ _,_ ⌟!}

-- BinOp : Set
-- BinOp = ∀ {A : Set} {B : A → Set} {C : (a : A) → B a → Set} → (a : A) → (b : B a) → C a b

-- BinOp′ : Set
-- BinOp′ = ∀ {A : Set} {B : Set} {C : Set} → A → B → C

-- ⌞_⌟ : BinOp → BinOp′
-- ⌞ _⊕_ ⌟ = ?
