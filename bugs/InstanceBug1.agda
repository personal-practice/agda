open import Eq

module InstanceBug1 (A : Set) {{_ : Eq A}} where

postulate a : A
