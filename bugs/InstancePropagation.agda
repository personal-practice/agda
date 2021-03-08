-- https://github.com/agda/agda/issues/5093
module InstancePropagation where

postulate Eq : Set → Set

module M1 (A : Set) {{_ : Eq A}} where
  postulate B : Set
  variable  n : B
  postulate P : B → Set

module M2 (A : Set) ⦃_ : Eq A⦄ where
  open M1 A
  postulate p : P n  -- No instance of type Eq A
