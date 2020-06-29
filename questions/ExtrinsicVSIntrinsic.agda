{-# OPTIONS --type-in-type #-}
module ExtrinsicVSIntrinsic where

open import Data.Product
open import Data.List hiding ([_])
open import Data.Nat hiding (_^_)

open import Relation.Binary.PropositionalEquality hiding ([_])

-- open import Prelude.Lists

private
  variable
    A : Set
    X : Set → Set

_^_ : Set → ℕ → Set
A ^ 0     = A
A ^ suc n = A × (A ^ n)

record ListLike (X : Set → Set) : Set where
  field
    nil : X A
    cons : A → X A → X A
open ListLike {{...}} public

instance
  LL-List : ListLike List
  LL-List = record {nil = []; cons = _∷_}

[_] : ∀ {n} {{_ : ListLike X}} → ℕ ^ n → X ℕ
[_] {n = zero}  x        = cons x nil
[_] {n = suc n} (x , xs) = cons x [ xs ]

splitAt₁ : List A → ℕ → List A × List A
splitAt₁ xs i = take i xs , drop i xs

_ : splitAt₁ [ 0 , 1 , 2 ] 1 ≡ ([ 0 ] , [ 1 , 2 ])
_ = refl

splitAt₂ : List A → ℕ → List A × List A
splitAt₂ xs zero = [] , xs
splitAt₂ [] (suc i) = [] , []
splitAt₂ (x ∷ xs) (suc i) = map₁ (x ∷_) (splitAt₂ xs i)

_ : splitAt₂ [ 0 , 1 , 2 ] 1 ≡ ([ 0 ] , [ 1 , 2 ])
_ = refl
