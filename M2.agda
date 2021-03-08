{-# OPTIONS -v try:100 #-}
open import Prelude.Init
open import Prelude.Decidable
open import Prelude.DecEq

open import Prelude.Generics
open import Prelude.Tactics.Try

module M2 where -- (A : Set) {{_ : DecEq A}} where

open import M1 ℕ

test : 5 ~ 5
-- test = auto
-- test = auto {{Dec-~}}
test = try auto ∶- [ quote Dec-~ ∙ ]
