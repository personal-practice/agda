{-# OPTIONS -v adhoc:100 #-}
module MacroAlt4 where

open import Prelude.Init
open Meta
open L.Mem
open import Prelude.Generics hiding (unifyStrict)
open import Prelude.Applicative
open import Prelude.Monad
open import Prelude.Nary
open import Prelude.Show
open Debug ("adhoc" , 100)

ensureNoMetas : Term → TC ⊤
ensureNoMetas = λ where
  (var x args) → noMetaArgs args
  (con c args) → noMetaArgs args
  (def f args) → noMetaArgs args
  (lam v (abs _ t)) → ensureNoMetas t
  (pat-lam cs args) → noMetaClauses cs *> noMetaArgs args
  (pi a b) → noMetaArg a *> noMetaAbs b
  (agda-sort s) → noMetaSort s
  (lit l) → pure _
  (meta x x₁) → error "meta found!!" -- blockOnMeta x
  unknown → pure _
   where
    noMetaArg : Arg Term → TC ⊤
    noMetaArg (arg _ v) = ensureNoMetas v

    noMetaArgs : List (Arg Term) → TC ⊤
    noMetaArgs [] = pure _
    noMetaArgs (v ∷ vs) = noMetaArg v *> noMetaArgs vs

    noMetaClause : Clause → TC ⊤
    noMetaClause (clause ps t) = ensureNoMetas t
    noMetaClause (absurd-clause ps) = pure _

    noMetaClauses : List Clause → TC ⊤
    noMetaClauses [] = pure _
    noMetaClauses (c ∷ cs) = noMetaClause c *> noMetaClauses cs

    noMetaAbs : Abs Term → TC ⊤
    noMetaAbs (abs _ v) = ensureNoMetas v

    noMetaSort : Sort → TC ⊤
    noMetaSort (set t) = ensureNoMetas t
    noMetaSort _       = pure _

unifyStrict : Hole → Term → TC ⊤
unifyStrict hole x = do
  -- unify hole x
  -- instantiate hole >>= ensureNoMetas
  print "———————————————————————————————————————"
  printTerm "x" x
  unify hole x
  (x′ ∷ hole′ ∷ []) ← mapM instantiate (x ∷ hole ∷ [])
    where _ → _IMPOSSIBLE_
  printTerm "hole′" hole′
  printTerm "x′" x′
  ensureNoMetas hole′
  printLn "No metas found :)"

macro
  solve : Term → TC ⊤
  solve hole = inferType hole >>= λ where
    (def (quote _∈_) (hArg _ ∷ hArg _ ∷ vArg x ∷ vArg xs ∷ _)) →
      case xs of λ where
        (def (quote _++_) (hArg _ ∷ hArg _ ∷ vArg ys ∷ vArg zs ∷ _)) → do
          printLn $ show x ◇ " ∈? " ◇ show ys ◇ " ++ " ◇ show zs
          t ← quoteTC (L.Mem.∈-++⁺ʳ _ (here refl))
          unifyStrict hole (lit (char 'a'))
            <|> unifyStrict hole t
 -- (def (quote L.Mem.∈-++⁺ʳ)
 --              ( vArg unknown
 --              ∷ vArg (con (quote Any.here) (vArg (con (quote refl) []) ∷ []))
 --              ∷ []))
            -- <|> unifyStrict hole (def (quote L.Mem.∈-++⁺ʳ)
            --   ( vArg xs
            --   ∷ vArg (con (quote Any.here) (vArg (con (quote refl) []) ∷ []))
            --   ∷ []))

        _ → error "not a _++_ list"
    _ → error "not a _∈_ type"

test : ∀ (xs : List ℕ) → 0 ∈ xs ++ (0 ∷ [])
test xs = L.Mem.∈-++⁺ʳ _ (here refl)   -- works
test xs = L.Mem.∈-++⁺ʳ xs (here refl)  -- works
test xs = solve
