-- ** using typeclasses naively ~> cannot prove termination
module RobustCollectionIdeal where

open import Data.List.Membership.Propositional.Properties

open import Prelude.Init
open import Prelude.Lists
open import Prelude.Nary

open import Prelude.Collections

-- enable automatic collection
variable
  X Y Z : Set
instance
  H-List : ∀ ⦃ _ : X has Y ⦄ → List X has Y
  H-List = collectFromList

  H-× : ∀ ⦃ _ : Y has Z ⦄ → (X × Y) has Z
  H-× = collectFromPairʳ

-----------------------------
-- ** Expressions

data Exp : Set
Exps = List Exp
VExps = List (⊤ × Exps)

Payload = ℕ × String × ℕ × String

data Exp where
  single : Payload → Exp
  split : Exps → Exp
  vsplit : VExps → Exp

-----------------------------
-- ** Collectors

mkCollect : ∀ {X : Set} ⦃ _ : Exp has X ⦄ → (Payload → List X) → Exp → List X
mkCollect {X = X} mk = case_of λ where
  (single s)   → mk s
  (split es)   → collect es
  (vsplit ves) → collect ves

-- nums

instance
  {-# TERMINATING #-}
  Hℕ : Exp has ℕ
  Hℕ .collect = mkCollect λ{ (n , _ , x , _) → ⟦ n , x ⟧ }

nums : ∀ {A : Set} ⦃ _ : A has ℕ ⦄ → A → List ℕ
nums = collect

private
  _ : nums (single (1 , "" , 2 , ""))
   ++ nums (vsplit [ (tt , [ single (3 , "" , 4 , "") ]) ])
   ++ nums [ (single (5 , "" , 6 , "")) ]
   ++ nums [ (tt , [ single (7 , "" , 8 , "") ]) ]
    ≡ ⟦ 1 , 2 , 3 , 4 , 5 , 6 , 7 , 8 ⟧
  _ = refl

-- names

Name = String ⊎ String

instance
  {-# TERMINATING #-}
  HN : Exp has Name
  HN .collect = mkCollect λ{ (_ , l , _ , r) → ⟦ inj₁ l , inj₂ r ⟧ }

names : ∀ {A : Set} ⦃ _ : A has Name ⦄ → A → List Name
names = collect

private
  _ : names (single (1 , "a" , 2 , "b"))
   ++ names (vsplit [ (tt , [ single (3 , "c" , 4 , "d") ]) ])
   ++ names [ (single (5 , "e" , 6 , "f")) ]
   ++ names [ (tt , [ single (7 , "g" , 8 , "h") ]) ]
    ≡ ⟦ inj₁ "a" , inj₂ "b" , inj₁ "c" , inj₂ "d" , inj₁ "e" , inj₂ "f" , inj₁ "g" , inj₂ "h" ⟧
  _ = refl

-- subterms

instance
  {-# TERMINATING #-}
  HS : Exp has Exp
  HS .collect e = e ∷ (case e of λ where
    (single _)   → []
    (split es)   → collect es
    (vsplit ves) → collect ves)

subterms : ∀ {A : Set} ⦃ _ : A has Exp ⦄ → A → Exps
subterms = collect

private
  _ : subterms (vsplit [ (tt , [ single (3 , "" , 4 , "") ])])
    ≡ ⟦ vsplit [ (tt , [ single (3 , "" , 4 , "") ])]
      , single (3 , "" , 4 , "") ⟧
  _ = refl

-----------------------------
-- ** Lemmas

variable
  e : Exp
  es : Exps
  ves : VExps

subterms⊆ᵉˢ : es ⊆ subterms es
subterms⊆ᵉˢ {es = e ∷ es} (here refl) = here refl
subterms⊆ᵉˢ {es = e ∷ es} (there p) = there (∈-++⁺ʳ _ (subterms⊆ᵉˢ p))

subterms⊆ᵛᵉˢ : (tt , es) ∈ ves → es ⊆ subterms ves
subterms⊆ᵛᵉˢ {ves = (_ , es) ∷ ves} (here refl) = ∈-++⁺ˡ ∘ subterms⊆ᵉˢ
subterms⊆ᵛᵉˢ {ves = (_ , es) ∷ ves} (there p)   = ∈-++⁺ʳ _ ∘ subterms⊆ᵛᵉˢ p

subterms-names⊆ : e ∈ subterms es → names e ⊆ names es
subterms-names⊆ᵛ : e ∈ subterms ves → names e ⊆ names ves

subterms-names⊆ {es = e ∷ es} (here refl) = ∈-++⁺ˡ
subterms-names⊆ {es = e ∷ es} (there p)
  with ∈-++⁻ _ p
... | inj₂ p′ = ∈-++⁺ʳ _ ∘ subterms-names⊆ {es = es} p′
... | inj₁ p′
  with e | p′
... | single _   | ()
... | split es′  | p″ = ∈-++⁺ˡ ∘ subterms-names⊆ {es = es′} p″
... | vsplit ves | p″ = ∈-++⁺ˡ ∘ subterms-names⊆ᵛ {ves = ves} p″

subterms-names⊆ᵛ {ves = (tt , []) ∷ ves} p = ∈-++⁺ʳ _ ∘ subterms-names⊆ᵛ {ves = ves} p
subterms-names⊆ᵛ {ves = (tt , es) ∷ ves} p
  with ∈-++⁻ (subterms es) p
... | inj₁ p′ = ∈-++⁺ˡ ∘ subterms-names⊆ {es = es} p′
... | inj₂ p′ = ∈-++⁺ʳ _ ∘ subterms-names⊆ᵛ {ves = ves} p′
