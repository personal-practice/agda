module NatWellFounded where

open import Function
open import Level
open import Data.Nat
open import Data.Nat.Induction
open import Data.Nat.Properties

open import Relation.Binary

open import Induction.WellFounded

-- 0) *** Non-termination can lead to paradoxes
{-# NON_TERMINATING #-}
f : ∀ {A B : Set} → A → B
f x = f x

-- 1) *** termination check fails
-- f : ℕ → ℕ
-- f 0 = 0
-- f n = f ⌊ n /2⌋

-- 2) *** Custom well-founded

/2-less : ∀ n → ⌊ n /2⌋ ≤ n
/2-less zero          = z≤n
/2-less (suc zero)    = z≤n
/2-less (suc (suc n)) = s≤s (≤-trans (/2-less n) (n≤1+n _))

{-
module Accessibility {A : Set} (_≲_ : Rel A 0ℓ) where

  data Acc (n : A) : Set where
    acc : (∀ m → m ≲ n → Acc m) → Acc n

  WellFounded : Set
  WellFounded = ∀ n → Acc n

open Accessibility {A = ℕ} _<_

<-wf : WellFounded
<-wf n = acc (go n)
  where
    go : ∀ n m → m < n → Acc m
    go (ℕ.suc n) ℕ.zero m<n = Accessibility.acc λ _ ()
    go (ℕ.suc n) (ℕ.suc m) (s≤s m<n) = Accessibility.acc λ o o<sm → go n o (<-transˡ o<sm m<n)

f : ℕ → ℕ
f n = go _ (<-wf n)
  where
    go : ∀ n → Acc n → ℕ
    go zero    _       = 0
    go (suc n) (acc a) = go ⌊ n /2⌋ (a _ (s≤s $ /2-less _))

-- 2') *** termination fails if not inlinining accessibility of n/2
{-# TERMINATING #-}
f′ : ℕ → ℕ
f′ n = go _ (<-wf n)
  where
    go : ∀ n → Acc n → ℕ
    go zero    _       = 0
    go (suc n) (acc a) = go ⌊ n /2⌋ /2-acc
      where
        /2-acc : Acc ⌊ n /2⌋
        /2-acc = a _ (s≤s $ /2-less _)
-}

-- 3) *** WF from Agda-Stdlib
<-wf : WellFounded _<_
<-wf n = acc $ go n
  where
    go : ∀ n m → m < n → Acc _<_ m
    go (suc n) zero    m<n       = acc λ _ ()
    go (suc n) (suc m) (s≤s m<n) = acc λ o o<sm → go n o (<-transˡ o<sm m<n)

<-rec′ = All.wfRec <-wf 0ℓ
-- ≈ Data.Nat.Induction.<-rec

f′ : ℕ → ℕ
f′ = <-rec′ _ go
  where
    go : ∀ n → (∀ m → m < n → ℕ) → ℕ
    go zero    _ = 0
    go (suc n) r = r ⌊ n /2⌋ (s≤s $ /2-less _)
