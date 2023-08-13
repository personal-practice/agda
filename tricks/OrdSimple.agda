open import Prelude.Init; open SetAsType
open import Prelude.Ord
open import Prelude.Generics
open import Prelude.DecEq
open import Prelude.Decidable

record X : Type where
  field n : ℕ
        s : String
open X public
unquoteDecl DecEq-X = DERIVE DecEq [ quote X , DecEq-X ]
-- unquoteDecl Ord-X DecOrd-X OrdLaws-X =
--   DERIVE Ord [ quote X , Ord-X , DecOrd-X , OrdLaws-X ]

private variable A : Type ℓ; B : Type ℓ′

on<-dec : ⦃ _ : Ord A ⦄ ⦃ _ : Ord B ⦄ ⦃ dec< : _<_ {A = A} ⁇² ⦄ →
  ∀ (f : B → A) → (_<_ on f) ⁇²
on<-dec f {x}{y} with ¿ f x < f y ¿
... | yes x< = ⁇ yes x<
... | no  x≮ = ⁇ no x≮

on≤-dec : ⦃ _ : Ord A ⦄ ⦃ _ : Ord B ⦄ ⦃ dec≤ : _≤_ {A = A} ⁇² ⦄ →
  ∀ (f : B → A) → (_≤_ on f) ⁇²
on≤-dec f {x}{y} with ¿ f x ≤ f y ¿
... | yes x≤ = ⁇ yes x≤
... | no  x≰ = ⁇ no x≰

instance
  Ord-X : Ord X
  Ord-X = mkOrd< (_<_ on n)

  Dec-<X : _<_ {A = X} ⁇²
  Dec-<X {x}{y} = on<-dec ⦃ dec< = Dec-< ⦃ r = DecOrd-ℕ ⦄ ⦄ n {x}{y}

  Dec-≤X : _≤_ {A = X} ⁇²
  Dec-≤X {x}{y} = ⁇ ≤?-from-<? (dec² ⦃ Dec-<X {x}{y} ⦄) x y

  DecOrd-X : DecOrd X
  DecOrd-X = mkDecOrd< (λ x y → dec² ⦃ Dec-<X {x}{y} ⦄ x y)

postulate instance
  OrdLaws-X : OrdLaws X
  ·Ord-X : ·Ord X

instance
  Ord⁺⁺-X : Ord⁺⁺ X
  Ord⁺⁺-X = mkOrd⁺⁺
