module ReflectionModuleParams.File1 (A : Set) where

open import Function
open import Data.Unit; open import Data.List
open import Reflection; open import Reflection.Term

postulate
  P : Set → Set
  PA : P A

♯0 : Arg Term
♯0 = vArg (var 0 [])

macro
  _∙A : Name → Term → TC ⊤
  n ∙A = flip unify $ def n [ ♯0 ]

  P∙A : Term → TC ⊤
  P∙A = flip unify $ def (quote P) [ ♯0 ]

  P∙A∙A : Term → TC ⊤
  P∙A∙A = flip unify $ def (quote P) (♯0 ∷ ♯0 ∷ [])

_ = P ∙A ∋ PA
_ = P∙A  ∋ PA
