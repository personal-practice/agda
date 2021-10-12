{-# OPTIONS -v adhoc:100 #-}
module MacroAlt2 where

open import Prelude.Init
open import Prelude.Generics
open import Prelude.Applicative
open import Prelude.Monad
open import Prelude.Nary
open import Prelude.Show
open Meta
open Debug ("adhoc" , 100)

open import Prelude.Decidable

macro
  solve : Term → TC ⊤
  solve hole@(meta holeM _) = do
    print $ "\n***************\nHole: " ◇ show hole ◇ "\n***************\n"
    ty ← normalise hole >>= inferType
    tryAll
      ( lit (char 'a')
      ∷ quote toWitness ∙⟦ quote tt ◆ ⟧
      ∷ quote _+_ ∙⟦ unknown ∣ unknown ⟧
      ∷ quote _+_ ∙⟦ lit (nat 0) ∣ unknown ⟧
      ∷ quote _+_ ∙⟦ unknown ∣ lit (nat 0) ⟧
      ∷ lit (nat 0)
      ∷ [])
    where
      unifyStrict : Term → TC ⊤
      unifyStrict x = do
        ty1 ← inferType hole
        ty2 ← inferType x
        print "———————————————————————————————————————"
        print (show x)
        print " : "
        print (show ty2)
        unify hole x
        x′ ← reduce x
        hole′ ← reduce hole
        x″ ← normalise x
        hole″ ← normalise hole
        print $ "hole′: " ◇ show hole′
        print $ "x′: " ◇ show x′
        print "-------------"
        print $ "hole″: " ◇ show hole″
        print $ "x″: " ◇ show x″
        ensureNoMetas hole″

      tryAll : List Term → TC ⊤
      tryAll = λ where
        [] → return tt
        (x ∷ xs) → unifyStrict x <|> tryAll xs
  solve _ = error "hole is not a meta!"

test : ℕ
test = solve
