module 2D-syntax where

open import Prelude.Init
open SetAsType
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.Ord

-- ** branching on decidable properties
private module _ {P X : Type} where

  YesHandler = P   → X
  NoHandler  = ¬ P → X

  _↙_ : Dec P → YesHandler × NoHandler → X
  p? ↙ (y , n) with p?
  ... | yes p = y p
  ... | no ¬p = n ¬p

  ↘ : YesHandler → NoHandler → YesHandler × NoHandler
  ↘ = _,_

_ : ℕ
_ =      (5 <? 10)
        ↙       ↘
  (λ 5< → 0)  (λ 5≮ → 1)

-- ** commuting diagrams
{-
  A──——f—─→B
  ∣        ∣
  a        b
  ↓        ↓
  A′──—g——→B′
-}

private

  commutes⦅_≫_≋_≫_⦆ : ∀ {A A′ B B′ : Type} →
    (A → A′) → (A′ → B′) → (A → B) → (B → B′) → Type
  commutes⦅ a ≫ g ≋ f ≫ b ⦆ = g ∘ a ≗ b ∘ f

  lemma : commutes⦅ (0 Nat.+_) ≫ (_+ 5) ≋ (_+ 5) ≫ (0 Nat.+_) ⦆
  lemma _ = refl

  record _—→_ (A B : Type) : Type where
    constructor mk
    field f : A → B
  syntax mk {A = A} {B = B} f = A ─ f ─ B

  record _⊗_⊗_⊗_ (A A′ B B′ : Type) : Type where
    constructor ∣∣
    field a : A → A′
          b : B → B′

  id′ : ∀ {A : Type} → A → A
  id′ = id
  syntax id′ x = ∣ x

  _∣_ : ∀ {A : Type} {B : Type} → A → B → A × B
  _∣_ = _,_

  commutes:_ : ∀ {A A′ B B′} →
    (A —→ B) × (A ⊗ A′ ⊗ B ⊗ B′) × (A′ —→ B′) → Type
  commutes: (mk f , ∣∣ a b , mk g) = commutes⦅ a ≫ g ≋ f ≫ b ⦆

  infix  -2 commutes:_
  infixr -1 _∣_
  infix  2 id′
  infix  3 mk

  postulate
    A A′ B B′ : Type
    a : A → A′
    g : A′ → B′
    f : A → B
    b : B → B′
    prf : commutes⦅ a ≫ g ≋ f ≫ b ⦆

  _ : commutes:
    A  ─ f ─ B
    ∣       ∣∣
    a        b
    ∣        ∣
   (A′ ─ g ─ B′)
  _ = prf
