{-# OPTIONS -v eta:100 #-}
module DeferredConstructors where

open import Prelude.Init
open Meta
open import Prelude.Generics
open import Prelude.Monad
open import Prelude.Semigroup
open import Prelude.Show
open import Prelude.Functor
open import Prelude.Tactics
open import Prelude.Lists
open import Prelude.ToN
open import Prelude.ToList

-- data X : ℕ → String → Set where
--   base : ∀ {s} → X 1 s
--   step : ∀ {n m s} → X n s → X m s → X (n + m) s
--    : ∀ {n m s} → X n s → X m s → X (n + m) s

--
record Num (A : Set) : Set where
  field nums : A → List ℕ
open Num ⦃...⦄

instance
  Num-ℕ : Num ℕ
  Num-ℕ .nums = [_]

  Num-× : ∀ {A B : Set} → ⦃ Num A ⦄ → ⦃ Num B ⦄ → Num (A × B)
  Num-× .nums (x , y) = nums x ++ nums y

  Num-List : ∀ {A : Set} → ⦃ Num A ⦄ → Num (List A)
  Num-List .nums = concatMap nums

  Num-Char : Num Char
  Num-Char .nums = [_] ∘ toℕ

  Num-String : Num String
  Num-String .nums = nums ∘ toList
--

record BigRecord {n} (xs : List (Fin $ suc n)) : Set where
  field
    pr : All (_≢ 0F) xs

data X : ℕ → String → Set

module _ n s where
  private
    Xs : List (Fin $ suc n)
    Xs = [ 0F ]

  module [0] (𝕣 : BigRecord Xs) where
    open BigRecord 𝕣

    proof : All (_≢ 0F) Xs
    proof = pr

    C = X n s

module _ {s} where
  module [1] {_ : ¬Null $ nums s} where
    open [0] (1 + sum (nums s)) s public
    -- C = X 1

module _
  (x : X 1 "")
  {n m s}
  (_ : X n s)
  (_ : X m s)
  where
  module [2] where
    open [0] 1 public
    -- C = X (n + m) s

data X where
  [1] : η [1].C
  -- [2] : η ([2].C [1])
  -- [3] : η [3].C

-- private
--   _ : X 1 "one"
--   _ = base

--   _ : X 2 "two"
--   _ = step base base
