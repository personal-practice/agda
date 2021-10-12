{-# OPTIONS -v adhoc:100 #-}
module MacroAlt where

open import Prelude.Init
open import Prelude.Generics hiding (unifyStrict)
open import Prelude.Applicative
open import Prelude.Monad
open import Prelude.Nary
open import Prelude.Show
open Meta
open Debug ("adhoc" , 100)


{-# TERMINATING #-}
isSolved : Hole → Bool
isSolved = λ where
  (meta _ _) → false
  unknown    → false
  (var _ xs) → all isSolved (unArgs xs)
  (con _ xs) → all isSolved (unArgs xs)
  (def _ xs) → all isSolved (unArgs xs)
  (lam _ (abs _ t)) → isSolved t
  (pat-lam cs xs) → all isSolved (unArgs xs)
  (pi (arg _ t) (abs _ t′)) → isSolved t ∧ isSolved t′
  _ → true

-- f : ℕ → ℕ
-- f x =

macro
  solve : Term → TC ⊤
  solve hole@(meta holeM _) = do
    print $ "\n***************\nHole: " ◇ show hole ◇ "\n***************\n"
    ty ← normalise hole >>= inferType
    tryAll
      ( lit (char 'a')
      ∷ unknown
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
        let b = isSolved hole″
        print "-------------"
        print $ "solved?″: " ◇ show b
        if b then return tt else error "continue"

      tryAll : List Term → TC ⊤
      tryAll = λ where
        [] → return tt
        (x ∷ xs) → unifyStrict x <|> tryAll xs
  solve _ = error "hole is not a meta"

test : ℕ
test = solve
