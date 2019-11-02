------------------------------------------------------------------------
-- Limitations of record update.
------------------------------------------------------------------------
module RecordUpdate where

open import Data.Nat using (ℕ)
open import Data.Vec using (Vec; [])
variable n m : ℕ
record R (n m : ℕ) : Set where
  field
    vec₁ : Vec ℕ n
    vec₂ : Vec ℕ m
open R public
empty₁ : R n m → R 0 m
empty₁ r = record r { vec₁ = [] }
empty₂ : R n m → R n 0
empty₁ r = record r { vec₂ = [] }
