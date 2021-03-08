module SingletonRec where

open import Prelude.Init

data Exp : Set where
  ` : ℕ → Exp
  ∑_ : List Exp → Exp

collect : List Exp → List Exp
collect [] = []
collect (e ∷ []) = [ e ]
collect (e ∷ es) = collect [ e ] ++ collect es
