{-# OPTIONS -v adhoc:100 #-}
module MembershipProofs where

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

-- ** patterns

infix 0 ≫_
pattern ≫_ x = there x
pattern ⊠  = here refl

pattern ⊠⊥ = here ()

-- ** simple (closed) examples

_ : 1 ∈ (List ℕ ∋ ⟦ 1 , 2 , 3 , 4 , 5 ⟧)
-- _ = ⊠
_ = auto

_ : 2 ∈ (List ℕ ∋ ⟦ 1 , 2 , 3 , 4 , 5 ⟧)
-- _ = ≫ ⊠
_ = auto

_ : 5 ∈ (List ℕ ∋ ⟦ 1 , 2 , 3 , 4 , 5 ⟧)
-- _ = ≫ ≫ ≫ ≫ ⊠
_ = auto

_ : 5 ∈ (List ℕ ∋ ⟦ 1 , 2 , 3 , 4 , 5 ⟧) ++ xs
-- _ = ≫ ≫ ≫ ≫ ⊠
_ = auto

-- ** advanced (open) examples

open import Prelude.Generics hiding (failOnMeta; unifyStrict; instantiate)
open Meta
open Debug ("adhoc" , 100) renaming (print to print₀)

print : String → TC ⊤
print x = print₀ (x ◇ "\n")

pattern `auto = quote auto ∙

pattern _`++_ xs ys = quote _++_ ∙⟦ xs ∣ ys ⟧
pattern _`∈_ x xs = quote _∈_ ∙⟦ x ∣ xs ⟧

data View∈ : Set where
  ∈⟨_,_⟩⦅_,_⦆ : Term → Term → Term → Term → View∈
  ∅ : View∈

view∈ : Term → View∈
view∈ = λ where
  (def (quote _∈_) (hArg a ∷ hArg A ∷ vArg x ∷ vArg xs ∷ [])) → ∈⟨ a , A ⟩⦅ x , xs ⦆
  _ → ∅

data ViewList : Set where
  ∷⦅_,_⦆ : Term → Term → ViewList
  ++⦅_,_⦆ : Term → Term → ViewList
  ∅ : ViewList

viewList : Term → ViewList
viewList = λ where
  (con (quote L._∷_) args) →
    case vArgs args of λ where
      (x ∷ xs ∷ []) → ∷⦅ x , xs ⦆
      _ → ∅
  (def (quote _++_) args) →
    case vArgs args of λ where
      (xs ∷ ys ∷ []) → ++⦅ xs , ys ⦆
      _ → ∅
  _ → ∅

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

printTerm : String → Term → TC ⊤
printTerm s t = do
  ty ← inferType t
  print $ s ◇ ": {"
  print $ show ty
  print $ " ∋ "
  print $ show t
  print $ "}"

macro
  solve∈ : Hole → TC ⊤
  solve∈ hole@(meta holeM _) = do
    print $ "***************\nHole: " ◇ show hole ◇ "\n***************\n"
    ty ← normalise hole >>= inferType
    (∈⟨ a , A ⟩⦅ x , xs ⦆) ← return (view∈ ty)
      where ∅ → error "solve∈: can only solve holes of type ? ∈ ?"
    case viewList xs of λ where
      ∷⦅ y , ys ⦆ → do
        print $ "Recognized: " ◇ show x ◇ " ∈ " ◇ show y ◇ " ∷ " ◇ show ys
        -- try ⟦ quote Any.here ◆⟦ quote refl ◆ ⟧
        --     , quote Any.here ◆⟦ `auto ⟧
        --     , quote Any.there ◆⟦ `auto ⟧
        --     , `auto
        --     ⟧
        try ⟦ con (quote Any.here)
                  ( hArg a
                  ∷ hArg a
                  ∷ hArg A
                  -- ∷ hArg (def (quote _≡_) (vArg b))
                  ∷ vArg (con (quote refl)
                        ( hArg a
                        ∷ hArg A
                        ∷ hArg x
                        ∷ []
                        ))
                  ∷ []
                  )
            , quote Any.there ◆⟦ `auto ⟧
            , `auto
            ⟧
      ++⦅ ys , zs ⦆ → do
        print $ "Recognized: " ◇ show x ◇ " ∈ " ◇ show ys ◇ " ++ " ◇ show zs
        try ⟦ quote L.Mem.∈-++⁺ˡ ∙⟦ `auto ⟧
       -- def (quote L.Mem.∈-++⁺ˡ) (hArg? ∷ hArg? ∷ hArg x ∷ hArg xs ∷ hArg ys ∷ vArg `auto ∷ []
            , quote L.Mem.∈-++⁺ʳ ∙⟦ ys ∣ `auto ⟧
        -- def (quote L.Mem.∈-++⁺ʳ) (hArg? ∷ hArg? ∷ hArg x ∷ vArg xs ∷ hArg ys ∷ vArg `auto ∷ []
            , `auto
            ⟧
      ∅ → do
        print "Not recognized"
        fallback
    where
      -- fallback = unify hole `auto
      fallback = error "UNSOLVED"

      unifyStrict : Hole → Term → TC ⊤
      unifyStrict hole x = do
        ty1 ← inferType hole
        ty2 ← inferType x
        print "———————————————————————————————————————"
        print (show x)
        -- print " : "
        -- print (show ty2)
        noConstraints $ unify hole x
        x′ ← reduce x
        hole′ ← reduce hole
        -- printTerm "hole′" hole′
        -- printTerm "x′" x′
        x″ ← normalise x′
        hole″ ← normalise hole′
        print " ~> " >> printTerm "hole′" hole″
        -- printTerm "hole″" hole″
        -- printTerm "x″" x″
        let b = isSolved hole″
        -- print "-------------"
        -- print $ "solved?: " ◇ show b
        if b then return tt else error "continue"

      try : List Term → TC ⊤
      try = λ where
        [] → fallback
        (x ∷ xs) → unifyStrict hole x <|> try xs
  solve∈ _ = error "hole is not a meta"

_ : 0 ∈ (0 ∷ [])
-- _ = here refl
-- _ = here auto
-- _ = there auto
-- _ = auto
_ = solve∈

_ : 0 ∈ (0 ∷ 1 ∷ [])
_ = here refl
-- _ = solve∈

_ : 0 ∈ (0 ∷ 1 ∷ xs)
_ = here refl
-- _ = solve∈

-- 5∈ : 5 ∈ (List ℕ ∋ ⟦ 1 , 2 , 3 , 4 , 5 ⟧)
-- 5∈ = solve∈

-- 5∉ : 5 ∉ (List ℕ ∋ ⟦ 1 , 2 , 3 , 4 ⟧)
-- 5∉ = solve∈

-- 5∈ʳ : 5 ∈ xs ++ (List ℕ ∋ ⟦ 1 , 2 , 3 , 4 , 5 ⟧)
-- 5∈ʳ =  solve∈

-- 5∈ˡ : 1 ∈ xs ++ (1 ∷ []) -- ++ xs
-- 5∈ˡ = solve∈

-- 5∈ʳ : 0 ∈ xs ++ (0 ∷ [])
-- 5∈ʳ = solve∈

-- 5∈ˡ : 5 ∈ (List ℕ ∋ ⟦ 1 , 2 , 3 , 4 , 5 ⟧) ++ xs
-- 5∈ˡ = solve∈


-- -- ** negation

-- 0∉ : 0 ∉ (List ℕ ∋ ⟦ 1 , 2 , 3 , 4 , 5 ⟧)
-- 0∉ 0∈ = case 0∈ of λ where
--   ⊠⊥
--   (≫ ≫ ⊠⊥)
--   (≫ ≫ ≫ ⊠⊥)
--   (≫ ≫ ≫ ≫ ⊠⊥)

-- _ : 0 ∉ (List ℕ ∋ ⟦ 1 , 2 , 3 , 4 , 5 ⟧)
-- _ = solve∈

-- 0∉′ : 0 ∉ (List ℕ ∋ ⟦ 1 , 2 , 3 , 4 , 5 ⟧)
-- 0∉′ 0∈ = contradict 0∈

{-
failOnUnknown : Term → TC ⊤
failOnUnknown = λ where
  (meta _ _) → pass
  (var _ xs) → failOnUnknownᵃˢ xs
  (con _ xs) → failOnUnknownᵃˢ xs
  (def _ xs) → failOnUnknownᵃˢ xs
  (lam _ (abs _ t)) → failOnUnknown t
  (pat-lam cs xs) → failOnUnknownᵃˢ xs
  (pi (arg _ t) (abs _ t′)) → failOnUnknown t >> failOnUnknown t′
  (agda-sort s) → failOnUnknownˢ s
  (lit _) → pass
  unknown → fail
   where
    fail pass : TC ⊤
    fail = error "found meta"
    pass = return tt

    failOnUnknownᵃ : Arg Term → TC ⊤
    failOnUnknownᵃ (vArg x) = failOnUnknown x
    failOnUnknownᵃ _        = pass

    failOnUnknownᵃˢ : List (Arg Term) → TC ⊤
    failOnUnknownᵃˢ [] = pass
    failOnUnknownᵃˢ (x ∷ xs) = failOnUnknownᵃ x >> failOnUnknownᵃˢ xs

    failOnUnknownˢ : Sort → TC ⊤
    failOnUnknownˢ = λ where
      (set t) → failOnUnknown t
      (lit _) → pass
      unknown → fail

    failOnUnknownᶜ : Clause → TC ⊤
    failOnUnknownᶜ = λ where
      (clause _ t) → failOnUnknown t
      (absurd-clause _) → pass

unifyStrict : Hole → Term → TC ⊤
unifyStrict hole x = do
  ty ← inferType hole
  print $ "x: " ◇ show x
  unify hole x
  hole′ ← reduce hole
  print $ "Hole′: " ◇ show hole′
  hole″ ← noConstraints $ checkType hole′ ty
  print $ "Hole″: " ◇ show hole′
  case hole″ of λ where
    (meta _ _) → error "hole is still an unsolved meta, aborting unification"
    _ → failOnUnknown hole′
-}

{-
countMetas : Term → ℕ
countMetas = λ where
  (meta _ _) → 1
  (var _ xs) → countMetasᵃˢ xs
  (con _ xs) → countMetasᵃˢ xs
  (def _ xs) → countMetasᵃˢ xs
  (lam _ (abs _ t)) → countMetas t
  (pat-lam cs xs) → countMetasᵃˢ xs
  (pi (arg _ t) (abs _ t′)) → countMetas t + countMetas t′
  (agda-sort s) → countMetasˢ s
  (lit _) → 0
  unknown → 1
   where
    countMetasᵃˢ : List (Arg Term) → ℕ
    countMetasᵃˢ [] = 0
    countMetasᵃˢ (arg _ x ∷ xs) = countMetas x + countMetasᵃˢ xs

    countMetasˢ : Sort → ℕ
    countMetasˢ = λ where
      (set t) → countMetas t
      (lit _) → 0
      unknown → 1

    countMetasᶜ : Clause → ℕ
    countMetasᶜ = λ where
      (clause _ t) → countMetas t
      (absurd-clause _) → 0

unifyStrict : Hole → Term → TC ⊤
unifyStrict hole x = do
  print $ "x: " ◇ show x
  let n = countMetas x
  unify hole x
  hole′ ← instantiate hole
  print $ "Hole′: " ◇ show hole′
  let n′ = countMetas hole′
  if ⌊ n′ >? n ⌋ then error "new unsolved metas, aborting unification" else return tt
-}

{-
instantiate : Term → TC Term
instantiate = normalise

unifyStrict : Hole → Term → TC ⊤
unifyStrict hole x = do
  print $ "x: " ◇ show x
  unify hole x
  hole′ ← instantiate hole
  print $ "Hole′: " ◇ show hole′
  case hole′ of λ where
    (meta _ _) → error "hole is still an unsolved meta, aborting unification"
    _ → return tt
-}

{-
data View () : Set where

  _`∷_ : Term → Term → View (

  _`++_

macro
  solve∈ : Hole → TC ⊤
  solve∈ hole = do
    print $ "Hole: " ◇ show hole
    ty ← inferType hole
    print $ "Ty: " ◇ show ty
    -- inferType hole >>= view >≡> λ where
    case view ty of λ where
      (x `∈ xs) → case view xs of λ where
        (x `∷ xs)   → here refl <|> there solve∈
        (xs `++ ys) → L.Mem.∈-++⁺ˡ solve∈ <|> L.Mem.∈-++⁺ʳ xs solve∈
        _

      -- x ∈ xs ++ ys
      (just (x , xs , ys)) → do
        print $ "Recognized: " ◇ show (x , xs , ys)
        try ⟦ -- def (quote L.Mem.∈-++⁺ˡ) (hArg? ∷ hArg? ∷ hArg x ∷ hArg xs ∷ hArg ys ∷ vArg `auto ∷ [])
              quote L.Mem.∈-++⁺ˡ ∙⟦ `auto ⟧
            , quote L.Mem.∈-++⁺ʳ ∙⟦ xs ∣ `auto ⟧
            ⟧
        -- try ⟦ def (quote L.Mem.∈-++⁺ˡ) (hArg? ∷ hArg? ∷ hArg x ∷ hArg xs ∷ hArg ys ∷ vArg `auto ∷ [])
        --     , def (quote L.Mem.∈-++⁺ʳ) (hArg? ∷ hArg? ∷ hArg x ∷ vArg xs ∷ hArg ys ∷ vArg `auto ∷ [])
        --     ⟧
      nothing → do

print "Not recognized"
-}

{-
similarity : Term → Term → ℕ
similarity t t′ = length $ L.takeWhile (uncurry _≟_) (zip (showL t) (showL t′))
  where showL = Str.toList ∘ show

-- sortOn : ∀ {A B : Set} → ⟦ Ord A ⦄ → (B → A) → List B → List B
-- sortOn

choose : Hole → List Term → TC ⊤
choose hole xs = do
  ts ← mapM go xs
  let chosen = getMaxTerm ts
  unify hole chosen
  where
    go : Term → TC (Term × ℕ)
    go t = runSpeculative $ fmap (_, false) $ do
      ty1 ← inferType hole
      ty2 ← inferType t
      comp ← compatible? ty1 ty2
      print "———————————————————————————————————————"
      print (show t)
      print " : "
      print (show ty2)
      print $ "ty1 ~? ty2: " ◇ show comp
      unify hole t
      t′ ← reduce t
      hole′ ← reduce hole
      print $ "hole′: " ◇ show hole′
      print $ "t′: " ◇ show t′
      return $ (t , similarity hole′ t′)

    -- bubblesort
    getMaxTerm : List (Term × ℕ) → Term
    getMaxTerm [] = `auto
    getMaxTerm ((t , _) ∷ []) = t
    getMaxTerm ((t , n) ∷ (t′ , n′) ∷ ts) =
      if ⌊ n >? n′ ⌋ then
        getMaxTerm ((t , n) ∷ ts)
      else
        getMaxTerm ((t′ , n′) ∷ ts)
      -- else
      --   go (curT , curN) ts
      -- where
      --   go : (Term × ℕ) → List (Term × ℕ) → Term
      --   go (curT , _) [] = t
      --   go (curT , curN) ((t , n) ∷ ts) =

macro
  solve∈ : Hole → TC ⊤
  solve∈ hole@(meta holeM _) = do
    print "***************"
    print $ "Hole: " ◇ show hole
    print "***************"
    ty ← inferType hole
    print $ "Ty: " ◇ show ty
    -- ty′ ← normalise hole >>= inferType
    case `∈-++ ty of λ where
      -- x ∈ xs ++ ys
      (just (x , xs , ys)) → do
        print $ "Recognized: " ◇ show x ◇ " ∈ " ◇ show xs ◇ " ++ " ◇ show ys
        choose hole ⟦ quote L.Mem.∈-++⁺ˡ ∙⟦ `auto ⟧
                    , quote L.Mem.∈-++⁺ʳ ∙⟦ xs ∣ `auto ⟧
                    , `auto
                    ⟧
      nothing → do
        print "Not recognized"
        fallback
    where
      fallback = unify hole `auto
  solve∈ _ = error "hole is not a meta"
-}
