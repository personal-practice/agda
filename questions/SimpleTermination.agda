------------------------------------------------------------------------
-- Limitations of termination checking.
------------------------------------------------------------------------
module SimpleTermination where

open import Data.Unit using (⊤; tt)

data A : Set where
  a b : A

f : A → ⊤
f a = tt
f b = f a
