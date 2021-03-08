{-# OPTIONS --allow-unsolved-metas #-}
open import Prelude.Init

module ModuleFunctorsL (A : Set) where

abstract
  S : Set
  S = List A

  ∅ : S
  ∅ = []

  singleton : A → S
  singleton = [_]

  _∪_ : Op₂ S
  s ∪ s′ = s ++ s′

  ∅-identity : Identity ∅ _∪_
  ∅-identity = L.++-identityˡ , L.++-identityʳ

  ∪-comm : Commutative _∪_
  ∪-comm = {!!}
