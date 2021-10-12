{-# OPTIONS -v Generics:100 #-}
module RecEqProofs where

open import Prelude.Init
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.Nary
open import Prelude.Ord
-- open import Prelude.Membership
open L.Mem
open import Prelude.Functor
open import Prelude.Applicative
open import Prelude.Monad
open import Prelude.Show

variable xs : List ℕ

open import Prelude.Generics
open Meta
open Debug ("Generics" , 100)

pattern `auto = quote auto ∙
pattern `refl = quote refl ◆
pattern `it   = quote it ∙

pattern _`++_ xs ys = quote _++_ ∙⟦ xs ∣ ys ⟧
pattern `Any P xs = quote Any ∙⟦ P ∣ xs ⟧

data ViewEq : Set where
  _`≡⟨_⟩_ : Term → Term × Term → Term → ViewEq
  ∅ : ViewEq

viewEq : Term → ViewEq
viewEq = λ where
  (def (quote _≡_) (hArg a ∷ hArg A ∷ vArg x ∷ vArg y ∷ [])) →
    x `≡⟨ a , A ⟩ y
  _ → ∅

solveEq′ : Hole × Meta × Type → TC ⊤
solveEq′ (hole , holeM , ty) = do
  I ← findDecEq (ℕ → ℕ)
  quoteTC I >>= printS
  -- (x `≡⟨ (a , A) ⟩ y) ← return (viewEq ty)
  --   where ∅ → error "solveEq: can only solve holes of type x ≡ y"
  -- `a ← unquoteTC {A = Level} a
  -- `A ← unquoteTC {A = Set `a} A
  -- `x ← unquoteTC {A = `A} x
  -- `y ← unquoteTC {A = `A} y
  -- I ← findDecEq `A
  -- return tt
  -- I ← unquoteTC {A = DecEq `A} `it
  -- case _≟_ ⦃ I ⦄ `x `y of λ where
  --   (yes x≡y) → quoteTC x≡y >>= unify hole
  --   (no  _) → error "solveEq: operands are not equal!"
  -- decide <|> unify hole `it
  -- where
      -- try ⟦ quote Any.here ◆⟦ `refl ⟧
      --     , quote Any.here ◆⟦ `auto ⟧
      --     , quote Any.here ◆⟦ `it ⟧
      --     , `auto
      --     , `it
      --     , quote Any.there ◆⟦ `auto ⟧
      --     ⟧
  -- where
  --   -- fallback = unify hole `auto
  --   fallback = error "UNSOLVED"

  --   try : List Term → TC ⊤
  --   try = λ where
  --     [] → fallback
  --     (x ∷ xs) → (withNormalisation true $ do
  --       print "———————————————————————————————————————"
  --       -- printS x -- printTerm "x" x
  --       unify hole x
  --       (x′ ∷ hole′ ∷ []) ← mapM instantiate (x ∷ hole ∷ [])
  --         where _ → _IMPOSSIBLE_
  --       -- printTerm "hole′" hole′
  --       -- printTerm "x′" x′
  --       print "* x"
  --       printLns
  --         ⟦ show x
  --         , show x′
  --         ⟧
  --       print ""
  --       print $ show hole ◇ " := " ◇ show hole′
  --       ensureNoMetas hole′
  --       ) <|> try xs

macro
  solveEq : Hole → TC ⊤
  solveEq hole@(meta holeM _) = do
    print $ "***************\nHole: " ◇ show hole ◇ "\n***************\n"
    ty ← normalise hole >>= inferType
    (x `≡⟨ (a , A) ⟩ y) ← return (viewEq ty)
    where ∅ → error "solveEq: can only solve holes of type x ≡ y"

    solveEq′ (hole , holeM , ty)
  solveEq _ = error "hole is not a meta"

_ : 0 ≡ 0
-- _ = here refl -- GREEN
-- _ = here auto -- GREEN
-- _ = here it -- GREEN
-- _ = auto -- GREEN
-- _ = there auto -- YELLOW
-- _ = here it -- RED
_ = solveEq

{-
_ : 0 ∈ (0 ∷ 1 ∷ [])
_ = here refl
-- _ = solveAny

_ : 0 ∈ (0 ∷ 1 ∷ xs)
_ = here refl
-- _ = solveAny
-}
