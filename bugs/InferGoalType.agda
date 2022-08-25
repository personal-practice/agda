-- https://github.com/agda/agda/issues/5750
open import Data.Unit; open import Data.List
open import Reflection

macro
  printGoalType : Term → TC ⊤
  printGoalType hole = do
    ty ← inferType hole
    typeError [ termErr ty ]

_ : ⊤ → ⊤
_ = printGoalType
