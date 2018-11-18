module Naturals where

data ℕ : Set where
  zero : ℕ 
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

_+_ : ℕ → ℕ → ℕ
zero  + n = n
suc m + n = suc (m + n)

_ : 2 + 3 ≡ 5
_ =
  begin
    2 + 3
  ≡⟨⟩
    suc (1 + 3)
  ≡⟨⟩
    suc (suc (0 + 3))
  ≡⟨⟩
    suc (suc 3)
  ≡⟨⟩
    5
  ∎

_ : 2 + 3 ≡ 5
_ = refl

_*_ : ℕ → ℕ → ℕ
zero    * _ = zero
(suc m) * n = n + (m * n)

_ : 2 * 3 ≡ 6
_ =
  begin
    2 * 3
  ≡⟨⟩
    3 + (1 * 3)
  ≡⟨⟩
    3 + (3 + (0 * 3))
  ≡⟨⟩
    3 + (3 + 0)
  ≡⟨⟩
    6
  ∎

_^_ : ℕ → ℕ → ℕ
n ^ zero    = 1
n ^ (suc m) = n * (n ^ m)

_ : 3 ^ 4 ≡ 81
_ =
  begin
    3 ^ 4
  ≡⟨⟩
    3 * (3 ^ 3)
  ≡⟨⟩
    3 * (3 * (3 ^ 2))
  ≡⟨⟩
    81
  ∎

_∸_ : ℕ → ℕ → ℕ
m       ∸ zero    = m
zero    ∸ (suc n) = zero
(suc m) ∸ (suc n) = m ∸ n

_ : 3 ∸ 2 ≡ 1
_ =
  begin
    3 ∸ 2
  ≡⟨⟩
    2 ∸ 1
  ≡⟨⟩
    1 ∸ 0
  ≡⟨⟩
    1
  ∎

_ : 2 ∸ 3 ≡ 0
_ =
  begin
    2 ∸ 3
  ≡⟨⟩
    1 ∸ 2
  ≡⟨⟩
    0 ∸ 1
  ≡⟨⟩
    0
  ∎

infixl 6 _+_ _∸_
infixl 7 _*_ _^_
{-# BUILTIN NATPLUS _+_ #-}
{-# BUILTIN NATTIMES _*_ #-}
{-# BUILTIN NATMINUS _∸_ #-}

-- Binary numbers

data Bin : Set where
  nil : Bin
  x0_ : Bin → Bin
  x1_ : Bin → Bin

-- e.g. 1011 ~ x1 x1 x0 x1 nil

inc : Bin → Bin
inc nil    = x1 nil
inc (x0 x) = x1 x
inc (x1 x) = x0 (inc x)

_ : inc (x0 x0 x0 nil) ≡ (x1 x0 x0 nil)
_ = refl
_ : inc (x1 x0 x0 nil) ≡ (x0 x1 x0 nil)
_ = refl
_ : inc (x0 x1 x0 nil) ≡ (x1 x1 x0 nil)
_ = refl
_ : inc (x1 x1 x0 nil) ≡ (x0 x0 x1 nil)
_ = refl
_ : inc (x0 x0 x1 nil) ≡ (x1 x0 x1 nil)
_ = refl

to : ℕ → Bin
to zero    = x0 nil
to (suc n) = inc (to n)

from : Bin → ℕ
from = from' 0
  where
    from' : ℕ → Bin → ℕ
    from' pow nil    = 0
    from' pow (x0 x) = from' (suc pow) x
    from' pow (x1 x) = 2 ^ pow + from' (suc pow) x
    

_ : from (x0 x0 x0 nil) ≡ 0
_ = refl
_ : to 0 ≡ x0 nil
_ = refl

_ : from (x1 x0 x0 nil) ≡ 1
_ = refl
_ : to 1 ≡ x1 nil
_ = refl

_ : from (x0 x1 x0 nil) ≡ 2
_ = refl
_ : to 2 ≡ x0 x1 nil
_ = refl

_ : from (x1 x1 x0 nil) ≡ 3
_ = refl
_ : to 3 ≡ x1 x1 nil
_ = refl

_ : from (x0 x0 x1 nil) ≡ 4
_ = refl
_ : to 4 ≡ x0 x0 x1 nil
_ = refl

-- import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _∸_)
