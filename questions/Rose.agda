module Rose where

open import Level
open import Function
open import Data.Empty
open import Data.List
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Nat
open import Data.Nat.Induction
open import Relation.Binary.PropositionalEquality using (refl)

variable
  A B : Set

data Rose (A : Set) : Set
Roses = List ∘ Rose

data Rose A where
  leaf  : A → Rose A
  roses : Roses A → Rose A


-- ** Problem: cannot use maps for lists, termination checking fails
module Problem where

  {-# TERMINATING #-}
  mapRose : (A → B) → Rose A → Rose B
  mapRose f (leaf x)   = leaf (f x)
  mapRose f (roses rs) = roses (map (mapRose f) rs)

  {-# TERMINATING #-}
  flatten : Rose A → List A
  flatten (leaf x)   = [ x ]
  flatten (roses rs) = concatMap flatten rs

-- ** Solution I: Mutually define a function on singlular elements and one acting on lists of those elements.
module Solution₁ where

  mapRose  : (A → B) → Rose A  → Rose B
  mapRoses : (A → B) → Roses A → Roses B

  mapRose f (leaf x)   = leaf (f x)
  mapRose f (roses rs) = roses (mapRoses f rs)

  mapRoses _ []       = []
  mapRoses f (r ∷ rs) = mapRose f r ∷ mapRoses f rs


  flatten  : Rose A → List A
  flattens : Roses A → List A

  flatten (leaf x)   = [ x ]
  flatten (roses rs) = flattens rs

  flattens []       = []
  flattens (r ∷ rs) = flatten r ++ flattens rs

-- ** Solution II: Use a well-founded order to ensure termination
module Solution₂ where

  Accessible : (A → A → Set) → A → Set
  Accessible _<_ x = ∀ y → y < x → Acc _<_ y

  WellFounded : (A → A → Set) → Set
  WellFounded _<_ = ∀ x → Acc _<_ x

  _≺_ : Rose A → Rose A → Set
  r ≺ roses rs = r ∈ rs
  _ ≺ leaf _   = ⊥

  ≺-wf : WellFounded (_≺_ {A})
  ≺-wf = acc ∘ _≻_
    where
      _≻_ : ∀ r r′ → r′ ≺ r → Acc _≺_ r′
      (roses .(r′ ∷ _) ≻ r′) (here refl) = acc (r′ ≻_)
      (roses (_  ∷ rs) ≻ r′) (there r′≺) = (roses rs ≻ r′) r′≺

  mapRose : (A → B) → Rose A → Rose B
  mapRose {A}{B} f = go _ ∘ ≺-wf
    where
      go : (r : Rose A) → Acc _≺_ r → Rose B
      go (leaf x)   _       = leaf (f x)
      go (roses rs) (acc a) = roses (mapWith∈ rs (go _ ∘ a _))

  flatten : Rose A → List A
  flatten = go _ ∘ ≺-wf
    where
      go : (r : Rose A) → Acc _≺_ r → List A
      go (leaf x)   _       = [ x ]
      go (roses rs) (acc a) = concat (mapWith∈ rs (go _ ∘ a _))

-- ** Solution II′: Use a well-founded order to ensure termination (using stdlib's WellFounded)
open import Induction
open import Induction.WellFounded
module Solution₂′ where

  _≺_ : Rose A → Rose A → Set
  r ≺ roses rs = r ∈ rs
  _ ≺ leaf _   = ⊥

  ≺-wf : WellFounded (_≺_ {A})
  ≺-wf = acc ∘ _≻_
    where
      _≻_ : ∀ r r′ → r′ ≺ r → Acc _≺_ r′
      (roses .(r′ ∷ _) ≻ r′) (here refl) = acc (r′ ≻_)
      (roses (_  ∷ rs) ≻ r′) (there r′≺) = (roses rs ≻ r′) r′≺

  mapRose : (A → B) → Rose A → Rose B
  mapRose {A}{B} f = go _ ∘ ≺-wf
    where
      go : (r : Rose A) → Acc _≺_ r → Rose B
      go (leaf x)   _       = leaf (f x)
      go (roses rs) (acc a) = roses (mapWith∈ rs (go _ ∘ a _))

  flatten : Rose A → List A
  flatten = go _ ∘ ≺-wf
    where
      go : (r : Rose A) → Acc _≺_ r → List A
      go (leaf x)   _       = [ x ]
      go (roses rs) (acc a) = concat (mapWith∈ rs (go _ ∘ a _))

-- ** Solution III: Derive a well-founded order from an existing one on naturals
module Solution₃ where

  variable
    r  : Rose A
    rs : Roses A

  postulate
    -- assume we have a measure on trees, such as their height of a tree
    height  : Rose A → ℕ
    -- ... which *strictly* descreases when recursing to subtrees
    height∈ : r ∈ rs → height r < height (roses rs)

  _≺_ : Rose A → Rose A → Set
  _≺_ = _<_ on height

  ≺-wf : WellFounded (_≺_ {A})
  ≺-wf = InverseImage.wellFounded height <-wellFounded

  -- instead of writing out the recursion ourselves, let's use convenient stdlib definition
  ≺-rec : Recursor (WfRec (_≺_ {A}))
  ≺-rec = All.wfRec ≺-wf 0ℓ

  mapRose : (A → B) → Rose A → Rose B
  mapRose {A}{B} f = ≺-rec _ λ
    { (leaf x)   _   → leaf (f x)
    ; (roses rs) rec → roses (mapWith∈ rs (rec _ ∘ height∈)) }

  flatten : Rose A → List A
  flatten = All.wfRec ≺-wf 0ℓ _ λ
    { (leaf x)   _   → [ x ]
    ; (roses rs) rec → concat (mapWith∈ rs (rec _ ∘ height∈)) }
