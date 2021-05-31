module Match where

open import Prelude.Init
open import Prelude.DecEq
open import Prelude.Functor
open import Prelude.Applicative

Hole = Maybe
pattern ∗   = nothing
pattern ` x = just x

data X : Set where
  mkX[_,_] : ℕ → String → X
  sucX[_] : X → X
unquoteDecl DecEq-X = DERIVE DecEq [ quote X , DecEq-X ]

-- {-
-- 1. Manually
record _-matches-_ (A∗ : Set) (A : Set) : Set where
  field
    _~~_ : A → A∗ → Bool
open _-matches-_ ⦃ ... ⦄ public

match : ∀ {A : Set} ⦃ _ : DecEq A ⦄ → A → Maybe A → Bool
match a mx = M.fromMaybe true ⦇ pure a == mx ⦈

-- open Prelude.Generics

-- macro
--   create∗ : Name → Term → TC ⊤
--   create∗ n hole = do

-- unquoteDecl X∗ = create∗ (quote X)

data X∗ : Set where
  mkX[_,_] : Hole ℕ → Hole String → X∗
  sucX[_] : Hole X∗ → X∗

{-# TERMINATING #-}
unquoteDecl DecEq-X∗ = DERIVE DecEq [ quote X∗ , DecEq-X∗ ]

{-
X∗ : Set
X∗ = (Hole ℕ × Hole String)
   ⊎ Hole {!!}

inj₁ ∼ mkX
inj₂ ~ sucX

`mkX[_,_] : Hole ℕ → Hole String → X∗
`mkX[ hn , hs ] = inj₁ (hn , hs)
pattern `mkX[_,_] hn hs = inj₁ (hn , hs)

`sucX[_] : Hole X∗ → X∗
`sucX[ x ] = inj₂ x
pattern `sucX[_] x = inj₂ x
-}

instance
  MatchX : X∗ -matches- X
  MatchX ._~~_ mkX[ n , s ] mkX[ hn , hs ] = match n hn ∧ match s hs
  MatchX ._~~_ sucX[ x ]    sucX[ hx ]     = M.fromMaybe true $ (x ~~_) <$> hx
  MatchX ._~~_ _            _               = false

_ : T $ mkX[ 1 , "one" ] == mkX[ (0 + 1) , (Str.fromList $ 'o' ∷ 'n' ∷ 'e' ∷ []) ]
_ = tt

_ : T $ mkX[ 1 , "one" ] ~~ mkX[ ` 1 , ∗ ]
_ = tt
-- -}

{-
-- 2. Semi-manually (using a macro to automatically put in the holes in each constructor)
macro
  holify : Type → Term → TC ⊤
  holify ty hole = do
    let as , r = viewTy ty

    unify hole ty′

data X∗ : Set where
  mkX[_,_] : holify (ℕ → String → X)
unquoteDecl DecEq-X∗ = DERIVE DecEq [ quote X∗ , DecEq-X∗ ]
-}


-- generic X∗

{-

  mkX[ 1 , mkX[ 2 , ∎ ] ]
  ~~
  Cons "mkX" ⟦ lit 1 , Cons "mkX" ⟦ lit 2 , Cons "∎" ∎ ⟧ ⟧

-}



{-
open import Prelude.Nary

data Holy : Set₁ where
  Cons : String → List Holy → Holy
  `_   : {A : Set} ⦃ _ : DecEq A ⦄ → A → Holy
  ∗    : Holy

instance
  DecEq-Holy : DecEq Holy
  DecEq-Holy ._≟_ x y
    with x | y
  ... | ∗ | ∗ = yes refl
  ... | ∗ | Cons _ _ = no λ()
  ... | ∗ | ` _ = no λ()
  ... | ` _ | ∗ = no λ()
  ... | `_ {A} a | `_ {B} b = {!!}
  ... | ` _ | Cons _ _ = no λ()
  ... | Cons _ _ | ∗ = no λ()
  ... | Cons _ _ | ` _ = no λ()
  ... | Cons s as | Cons s′ as′
    with s ≟ s′
  ... | no s≢ = no λ{ refl → s≢ refl }
  ... | yes refl
    with as ≟ as′
  ... | no as≢ = no λ{ refl → as≢ refl }
  ... | yes refl = yes refl
-- unquoteDecl DecEq-Holy = DERIVE DecEq [ quote Holy , DecEq-Holy ]

_ : Holy
_ = Cons "mkX" ⟦ ` 1 , ∗ ⟧

record Matchy (A : Set) : Set₁ where
  field
    _~~_ : A → Holy → Bool
open Matchy ⦃ ... ⦄ public

instance
  MatchyX : Matchy X
  MatchyX ._~~_ mkX[ n , s ] h =
    case h of λ where
      ∗ → true
      (` x) → {!!}
      (Cons c as) → (c == "mkX") ∧ (as == ⟦ ` n , ` s ⟧)

_ : T $ mkX[ 1 , "one" ] ~~ Cons "mkX" ⟦ ` 1 , ∗ ⟧
_ = tt
-}
