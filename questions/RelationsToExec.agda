{-# OPTIONS -v THE:100 #-}
open import Prelude.Init
open import Prelude.Lists
open import Prelude.Decidable
open import Prelude.DecEq
open import Prelude.Ord
open import Prelude.General
open import Prelude.InferenceRules
open import Prelude.Semigroup
open import Prelude.Monad
open import Prelude.Show

X = ℕ

data C : Set where
  ⟦_⟧ : List ℕ × ℕ → C

private variable
  x n : X
  xs : List ℕ
  c c′ : C

data _—[_]→_ : C → X → C → Set where
  [1] :
    let tot = sum xs in
    ∙ ¬Null xs
    ∙ x ≥ tot
      ──────────────────────────
      ⟦ xs , n ⟧
      —[ x ]→
      ⟦ x ∷ xs , n + x ⟧

  [2] :
    ∙ Null xs
    ∙ n ≡ 0
      ──────────────────────────
      ⟦ xs , n ⟧
      —[ x ]→
      ⟦ x ∷ xs , n + x ⟧

step : C → X → Maybe C
step c@(⟦ xs , n ⟧) x =
  -- let ⟦ xs , n ⟧ = c in
  if ⌊ ¿ (
    let tot = sum xs in
      ¬Null xs
    × x ≥ tot
    ) ¿ ⌋
    then just ⟦ x ∷ xs , n + x ⟧
  else if ⌊ ¿ (
      Null xs
    × n ≡ 0
    ) ¿ ⌋
    then just ⟦ x ∷ xs , n + x ⟧
    else nothing

_ : step

-- open import Prelude.Generics
-- open Meta
-- open Debug ("THE" , 100)
-- macro
--   $deriveStep : Name × Name → Hole → TC ⊤
--   $deriveStep (f , rel) hole = do
--     print "***************************************88"
--     print $ "r: " ◇ show rel
--     Π[ _ ∶ vArg ℂ ] Π[ _ ∶ vArg 𝕏 ] Π[ _ ∶ _ ] (agda-sort (lit _)) ← getType rel
--       where _ → _IMPOSSIBLE_
--     print $ "C: " ◇ show ℂ
--     print $ "X: " ◇ show 𝕏

--     print $ "f: " ◇ show f
--     declareDef (vArg f) (vΠ[ "_" ∶ ℂ ] vΠ[ "_" ∶ 𝕏 ] (quote Maybe ∙⟦ ℂ ⟧))

--     data-type ps cs ← getDefinition rel
--       where _ → _IMPOSSIBLE_
--     print $ "DATATYPE {pars = " ◇ show ps ◇ "; cs = " ◇ show cs ◇ "}"

--     branches ← forM cs getInfo
--     deriveTerm


--     defineFun f [ clause mtel pc (`swap ◆⟦ t ⟧) ]


-- unquoteDecl step′ = $deriveStep (step′ , quote _—[_]→_)


-- module _ {b} {A : Set ℓ} {x y : A} where
--   redIfʸ : T b → (if b then x else y) ≡ x
--   redIfʸ p with ⟫ b | p
--   ... | ⟫ true | tt = refl

--   redIfⁿ : T (not b) → (if b then x else y) ≡ y
--   redIfⁿ p with ⟫ b | p
--   ... | ⟫ false | tt = refl

--   module _ {∗ : A} where
--     reduceIfʸ : T b → x ≡ ∗ → (if b then x else y) ≡ ∗
--     reduceIfʸ p refl = redIfʸ p

--     reduceIfʸ⁻ : T b → (if b then x else y) ≡ ∗ → x ≡ ∗
--     reduceIfʸ⁻ p refl = sym $ redIfʸ p

--     reduceIfⁿ : T (not b) → y ≡ ∗ → (if b then x else y) ≡ ∗
--     reduceIfⁿ p refl = redIfⁿ p

--     reduceIfⁿ⁻ : T (not b) → (if b then x else y) ≡ ∗ → y ≡ ∗
--     reduceIfⁿ⁻ p refl = sym $ redIfⁿ p

--     reduceIfⁿ≡ : T (not b) → ((if b then x else y) ≡ ∗) ≡ (y ≡ ∗)
--     reduceIfⁿ≡ = cong (_≡ ∗) ∘ redIfⁿ


-- module _ {x x′ c : C} {α : X} where
--   reduceʸ′ : just x′ ≡ just x → c —[ α ]→ x′ → c —[ α ]→ x
--   reduceʸ′ p = subst (c —[ α ]→_) (M.just-injective p)

-- module _ {b} {x x′ c : C} {α : X} {y : Maybe C} where
--   reduceʸ : T b → c —[ α ]→ x′ → (if b then just x′ else y) ≡ just x → c —[ α ]→ x
--   reduceʸ p P eq = subst (c —[ α ]→_) (M.just-injective $ trans (sym $ redIfʸ p) eq) P

--   reduceⁿ : T (not b) → c —[ α ]→ x′ → (if b then y else just x′) ≡ just x → c —[ α ]→ x
--   reduceⁿ p P eq = subst (c —[ α ]→_) (M.just-injective $ trans (sym $ redIfⁿ p) eq) P


-- step-computes-relation : c —[ x ]→ c′ ⇔ step c x ≡ just c′
-- step-computes-relation {c = c@(⟦ xs , n ⟧)}{x}{c′} = from , to
--   where
--     ℂ₂⇒¬ℂ₁ : (Null xs × n ≡ 0) → ¬ (let tot = sum xs in ¬Null xs × x ≥ tot)
--     ℂ₂⇒¬ℂ₁ (xs≡[] , _) (xs≢[] , _) = xs≢[] xs≡[]

--     from : c —[ x ]→ c′ → step c x ≡ just c′
--     from ([1] p₁ p₂)
--       = reduceIfʸ (fromWitness {Q = dec} (p₁ , p₂)) refl
--     from ([2] p₁ p₂)
--       = reduceIfⁿ (fromWitnessFalse {Q = dec} (ℂ₂⇒¬ℂ₁ (p₁ , p₂)))
--       $ reduceIfʸ (fromWitness {Q = dec} (p₁ , p₂)) refl

--     to : step c x ≡ just c′ → c —[ x ]→ c′
--     to eq
--       = case ¿ (let tot = sum xs in ¬Null xs × x ≥ tot) ¿ of λ where
--         (yes (p₁ , p₂)) →
--           reduceʸ′ (reduceIfʸ⁻ (fromWitness {Q = dec} (p₁ , p₂)) eq)
--                    ([1] p₁ p₂)
--         (no  ¬p) →
--           case ¿ (Null xs × n ≡ 0) ¿ of λ where
--             (yes (p₁ , p₂)) →
--               reduceʸ′ ( reduceIfʸ⁻ (fromWitness {Q = dec} (p₁ , p₂))
--                        $ reduceIfⁿ⁻ (fromWitnessFalse {Q = dec} ¬p) eq)
--                        ([2] p₁ p₂)
--             (no  ¬p′) →
--               case ( reduceIfⁿ⁻ (fromWitnessFalse {Q = dec} ¬p′)
--                    $ reduceIfⁿ⁻ (fromWitnessFalse {Q = dec} ¬p) eq
--                    ) of λ ()
