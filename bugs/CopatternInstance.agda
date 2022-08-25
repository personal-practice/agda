open import Data.List using (List; _++_)
open import Data.List.Properties using (++-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Algebra.Definitions using (Associative)

record Semigroup (A : Set) : Set where
  field _◇_ : A → A → A
open Semigroup ⦃...⦄

record AssociativeSemigroup (A : Set) : Set where
  field
    overlap ⦃ sm ⦄ : Semigroup A
    ◇-assocʳ : Associative _≡_ _◇_
open AssociativeSemigroup ⦃...⦄ public hiding (sm)

private variable A : Set
instance
  Semigroup-List : Semigroup (List A)
  Semigroup-List ._◇_ = _++_

  AssocSemigroup-List : AssociativeSemigroup (List A)
  -- AssocSemigroup-List = record {◇-assocʳ = ++-assoc}
  AssocSemigroup-List .◇-assocʳ = ++-assoc
