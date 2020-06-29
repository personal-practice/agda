open import Data.List

open import Prelude.DecEq

module Expansion0 (A : Set) {{_ : DecEq A}} where

data Ty : Set where
  unit : A → Ty
  pair : A → A → Ty
