# already reported, still open: https://github.com/agda/agda/issues/632
module InfixDisplay where

open import Data.Nat
open import Data.String
open import Data.List
open import Data.List.Relation.Unary.Any
open import Data.Product
open import Data.Bool
open import Relation.Binary.PropositionalEquality
  hiding ([_])

module M (A : Set) where
  postulate _⁇ : A → Set

open M ℕ
_ : 0 ⁇
_ = {!!}

_ : let open M ℕ in 0 ⁇
_ = {!!}
