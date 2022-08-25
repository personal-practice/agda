open import Prelude.Init
open import Prelude.DecEq
-- open import Prelude.Generics using (DERIVE; Derivable)

module Unquote (A : Set) where

-- postulate
--   -- DERIVE : ∀ (F : Set↑) → List (Name × Name) → TC ⊤
--   F : Set↑
--   DF : Derivable F

-- instance _ = DF

unquoteDecl f = DERIVE DecEq [ quote _×_ , f ]
