open import Prelude.Init
open import Prelude.DecEq
open Meta
open import Prelude.Generics
open import Prelude.Monad

record Countable (A : Set) : Set where
  field count : A → ℕ
open Countable ⦃...⦄

data λTerm : Set where
  APP : λTerm → λTerm → λTerm
  VAR : ℕ → λTerm

-- instance
--   Countable-λTerm : Countable λTerm
--   Countable-λTerm .count = λ where
--     (VAR _) → 1
--     (APP l r) → count l + count r

genCountVars : Name → Name → TC ⊤
genCountVars f n = do
  (record-type ∙count= _) ← getDefinition (quote Countable)
    where _ → _IMPOSSIBLE_
  declareDef (iArg f) (quote Countable ∙⟦ n ∙ ⟧)
  defineFun f [ ⟦⇒ ∙count= ◆⟦
    `λ⟦ quote VAR ◆⟦ ` 0 ⟧
        ⦅ [ "_" , vArg (quote ℕ ∙) ]
        ⦆⇒ lit (nat 1)
      ∣ quote APP ◆⟦ ` 1 ∣ ` 0 ⟧
        ⦅ ("l" , vArg (n ∙)) ∷ ("r" , vArg (n ∙)) ∷ []
        -- ⦆⇒ quote _+_ ∙⟦ quote count ∙⟦ ♯ 1 ⟧
        --               ∣ quote count ∙⟦ ♯ 0 ⟧
        --               ⟧
        ⦆⇒ quote _+_ ∙⟦ def (quote count) (iArg (f ∙) ∷ vArg (♯ 1) ∷ [])
                      ∣ def (quote count) (iArg (f ∙) ∷ vArg (♯ 0) ∷ [])
                      ⟧
      ⟧ ⟧ ⟧ ]

{- non-prelude version for Github issue #5745
open import Function
open import Data.Unit; open import Data.Product; open import Data.Nat; open import Data.List
open import Reflection
open import Reflection.Term

genCountVars : Name → Name → TC ⊤
genCountVars f n = do
  (record-type ∙count= _) ← getDefinition (quote Countable)
    where _ → typeError [ strErr "IMPOSSIBLE" ]
  declareDef (iArg f) (def (quote Countable) [ vArg (def n []) ])
  defineFun f
    [ clause [] [] (con ∙count= [ vArg $
        pat-lam
          ( clause [ "_" , vArg (def (quote ℕ) []) ]
                  [ vArg $ con (quote VAR) [ vArg (Pattern.var 0) ] ]
                  (lit $′ nat 1)
          ∷ clause (("l" , vArg (def n [])) ∷ ("r" , vArg (def n [])) ∷ [])
                  [ vArg $ con (quote APP) (vArg (Pattern.var 1) ∷ vArg (Pattern.var 0) ∷ []) ]
                  (def (quote _+_) ( vArg (def (quote count) [ vArg (var 1 []) ])
                                   ∷ vArg (def (quote count) [ vArg (var 0 []) ])
                                   ∷ []))
          ∷ [])
          []
    ]) ]
-}

{-# TERMINATING #-}
unquoteDecl Countable-λTerm = genCountVars Countable-λTerm (quote λTerm)

_ = count (VAR 0) ≡ 1 ∋ refl
_ = count (APP (VAR 0) (VAR 1)) ≡ 2 ∋ refl
