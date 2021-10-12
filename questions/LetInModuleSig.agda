module LetInModuleSig where

open import Data.Product
open import Data.Nat
open import Agda.Builtin.Equality

module H₁ (xy : ℕ × ℕ) (eq : proj₁ xy ≡ 0) where
  eq′ : proj₁ xy ≡ 0
  eq′ = eq

-- module H₂ (xy : ℕ × ℕ) let x , y = xy in (eq : x ≡ 0) where
--   eq′ : x ≡ 0
--   eq′ = eq
