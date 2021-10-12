{-# OPTIONS -v adhoc:100 #-}
module MacroAlt3 where

open import Prelude.Init
open L.Mem
open Meta
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
  (meta x x₁) → errorP "meta found!"
  -- (meta x x₁) → blockOnMeta x
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


module NewMeta where
  unifyStrict : Hole → Term → TC ⊤
  unifyStrict hole x = inferType hole >>= λ ty → do
    printLn $ show hole ◇ " :=? " ◇ show x
    m@(meta mm _) ← newMeta ty
      where _ → _IMPOSSIBLE_
    noConstraints (unify m x)
    noConstraints (unify hole m)
    -- normalise hole >>= ensureNoMetas
    printLn $ show hole ◇ " := " ◇ show x

module NoMeta where
  unifyStrict : Hole → Term → TC ⊤
  unifyStrict hole x = do
    -- unify hole x
    -- instantiate hole >>= ensureNoMetas
    -- print "———————————————————————————————————————"
    -- printTerm "x" x
    unify hole x
    hole ← normalise hole
    -- (x ∷ hole ∷ []) ← mapM instantiate (x ∷ hole ∷ [])
    --   where _ → _IMPOSSIBLE_
    -- printTerm "hole′" hole
    -- printTerm "x′" x
    ensureNoMetas hole
    printLn "No metas found :)"

-- open NewMeta
open NoMeta

pattern ⁇ = unknown
pattern `here x = quote Any.here ◆⟦ x ⟧
pattern `there x = quote Any.there ◆⟦ x ⟧
pattern `refl = quote refl ◆
pattern `∈-++⁺ˡ x = quote ∈-++⁺ʳ ∙⟦ x ⟧
pattern `∈-++⁺ʳ x y = quote ∈-++⁺ʳ ∙⟦ x ∣ y ⟧
pattern `[] = quote L.List.[] ◆
pattern _`∷_ x y = quote L._∷_ ◆⟦ x ∣ y ⟧
pattern `it = quote it ∙

macro
  solve : Term → TC ⊤
  solve hole =
    unifyStrict hole unknown
      <|> unifyStrict hole ⁇
      <|> unifyStrict hole (`here ⁇)
      <|> unifyStrict hole (`there ⁇)
      <|> unifyStrict hole (`here `refl)
      <|> unifyStrict hole (`there (`here ⁇))
      -- <|> unifyStrict hole (`there (`here `it))
      <|> unifyStrict hole (quote ∈-++⁺ʳ
      ∙⟦ unknown
       ∣ quote Any.here ◆⟦ quote refl ◆ ⟧
       ⟧)
      <|> unifyStrict hole (quote ∈-++⁺ʳ
      ∙⟦ (quote L._∷_ ◆⟦ unknown ∣ quote L.List.[] ◆ ⟧)
       ∣ quote Any.here ◆⟦ quote refl ◆ ⟧
       ⟧)
      -- <|> unifyStrict hole (`there (`here `refl))

    -- unifyStrict hole (lit (char 'a'))
    --   <|> unifyStrict hole unknown
    --   <|> unifyStrict hole (quote from⊤ ∙⟦ unknown ⟧)
    --   <|> unifyStrict hole (lit (nat 0))
    --   <|> unifyStrict hole (quote Any.there ◆⟦ unknown ⟧)
    --   <|> unifyStrict hole (quote Any.there ◆⟦ quote Any.here ◆⟦ quote refl ◆ ⟧ ⟧)
    --   <|> unifyStrict hole (quote ∈-++⁺ʳ ∙⟦ (quote L._∷_ ◆⟦ unknown ∣ quote L.List.[] ◆ ⟧)
    --                                       ∣ quote Any.here ◆⟦ quote refl ◆ ⟧ ⟧)
      -- <|> unifyStrict hole (quote Any.here ◆⟦ quote refl ◆ ⟧)

test : ℕ
test = F.toℕ (L.Any.index go)
  where
    go : 1 ∈ (0 ∷ 1 ∷ [])
    -- go = there (here it)
    -- go = _
    -- go = here _
    -- go = there _
    -- go = here refl
    -- go = there (here _)
    -- go = ∈-++⁺ʳ _ (here refl)
    -- go = ∈-++⁺ʳ (_ ∷ []) (here refl)
    -- go = there (here refl)
    -- go = ∈-++⁺ʳ (0 ∷ []) (here refl)
    go = solve

_ : test ≡ 1
_ = refl
