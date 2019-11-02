------------------------------------------------------------------------
-- Limitations of idiom brackets.
------------------------------------------------------------------------
module IdiomBrackets where

open import Data.Bool    using (Bool; _≟_; _∧_)
open import Data.Maybe   using (Maybe; nothing; map)

open import Relation.Nullary                      using (Dec; yes; no)
open import Relation.Nullary.Decidable            using (⌊_⌋)
open import Relation.Binary                       using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Level using (0ℓ)
open import Category.Functor       using (RawFunctor)
open import Category.Applicative   using (RawApplicative)
open import Data.Maybe.Categorical using (functor; applicative)
open RawFunctor {0ℓ} functor
open RawApplicative {0ℓ} applicative
_<*>_ = _⊛_ -- pfff...

data Expr : Set where
  ⊥    : Expr
  `_   : Bool → Expr
  _`∧_ : Expr → Expr → Expr
  _`=_ : Expr → Expr → Expr

⟦_⟧ : Expr → Maybe Bool
⟦ ⊥       ⟧ = nothing
⟦ ` x     ⟧ = ⦇ x ⦈
⟦ e `∧ e′ ⟧ = ⦇ ⟦ e ⟧ ∧ ⟦ e′ ⟧ ⦈
⟦ e `= e′ ⟧ = map ⌊_⌋ t -- ⦇ ⟦ e ⟧ ≟ ⟦ e′ ⟧ ⦈
  where
    t : Maybe (Dec (⟦ e ⟧ ≡ ⟦ e′ ⟧))
    t = {!⦇ ⟦ e ⟧ ≟ ⟦ e′ ⟧ ⦈!}
