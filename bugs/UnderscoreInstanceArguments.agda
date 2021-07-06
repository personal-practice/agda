-- Issue #5467
module UnderscoreInstanceArguments where

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

record Def (A : Set) : Set where
  field def : A
open Def ⦃...⦄

_ = ⦃ _ : Def Nat ⦄ → def ≡ 0 -- this works
_ = ⦃ Def Nat ⦄ → def ≡ 0 -- this fails
