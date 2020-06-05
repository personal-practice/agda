{- *** Thorsten Altenkirch: The symmetry of cubism (25/5) *** -}

{-# OPTIONS --cubical #-}
module AIM where

open import Data.Nat
-- open import Relation.Binary.PropositionalEquality
-- open import Agda.Primitive.Cubical
open import Agda.Primitive.Cubical renaming
  ( primINeg to ~_; primIMax to _∨_; primIMin to _∧_
  ; primHComp to hcomp; primTransp to transp; primComp to comp
  ; itIsOne to 1=1 )
open import Agda.Builtin.Cubical.Path
open import Agda.Builtin.Cubical.Glue

record Stream (A : Set) : Set where
  coinductive
  field
    hd : A
    tl : Stream A
open Stream public

from : ℕ → Stream ℕ
hd (from n) = n
tl (from n) = from (suc n)

mapStream : {A B : Set} → (A → B) → Stream A → Stream B
hd (mapStream f xs) = f (hd xs)
tl (mapStream f xs) = mapStream f (tl xs)

rfl : {A : Set} {a : A} → a ≡ a
rfl {A} {a} i = a

thm : (n : ℕ) → mapStream suc (from n) ≡ from (suc n)
hd (thm n i) = suc n
tl (thm n i) = thm (suc n) i

module _ {A : Set} where

  trans' : {a b c : A} → a ≡ b → b ≡ c → a ≡ c
  trans' {a = a} p q i = hcomp (λ j → λ {(i = i0) → a; (i = i1) → q j}) (p i)


f1 : ℕ → ℕ
f1 x = x

f2 : ℕ → ℕ
f2 x = x + 0


f-thm : f1 ≡ f2
f-thm i zero = zero
f-thm i (suc n) = suc (f-thm i n)
