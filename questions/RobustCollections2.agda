-- ** without well-founded recursion, hence need to inline map/concatMap
module RobustCollections2 where

open import Data.List.Membership.Propositional.Properties

open import Prelude.Init
open import Prelude.Lists
open import Prelude.Collections
open import Prelude.Nary

-----------------------------
-- ** Expressions

data Exp : Set
Exps = List Exp
VExps = List (⊤ × Exps)

data X : Set where
  mkX : ℕ → X

Payload = ℕ × String × X × String

data Exp where
  single : Payload → Exp
  split : Exps → Exp
  vsplit : VExps → Exp

data 𝔼 : Set where
  E : Exp → 𝔼
  ES : Exps → 𝔼
  VES : VExps → 𝔼
-- 𝔼 = Exp ⊎ Exps ⊎ VExps

variable
  x x′ : X
  e e′ : Exp
  es es′ : Exps
  ves ves′ : VExps

-----------------------------
-- ** Collectors

mkCollect : ∀ {X : Set} → (Payload → List X) → 𝔼 → List X
mkCollect {X = X} mk = go
  where
    go : 𝔼 → List X
    go (E (single s)) = mk s
    go (E (split es)) = go (ES es)
    go (E (vsplit ves)) = go (VES ves)
    go (ES []) = []
    go (ES (e ∷ es)) = go (E e) ++ go (ES es)
    go (VES []) = []
    go (VES ((_ , es) ∷ ves)) = go (ES es) ++ go (VES ves)

{- ** this does not pass termination checking; manually write `subterms`
mkCollect′ : ∀ {X : Set} → (Exp → (𝔼 → List X) → List X) → 𝔼 → List X
mkCollect′ {X = X} mk = go
  where
    go : 𝔼 → List X
    go (E e) = mk e go -- termination fails here
    go (ES []) = []
    go (ES (e ∷ es)) = go (E e) ++ go (ES es)
    go (VES []) = []
    go (VES ((_ , es) ∷ ves)) = go (ES es) ++ go (VES ves)

mkCollect : ∀ {X : Set} → (Payload → List X) → 𝔼 → List X
mkCollect mk = mkCollect′ λ e go → case e of λ
  { (single s)   → mk s
  ; (split es)   → go (ES es)
  ; (vsplit ves) → go (VES ves)
  }
-}

-- nums

nums𝔼 : 𝔼 → List ℕ
nums𝔼 = mkCollect λ{ (n , _ , mkX x , _) → ⟦ n , x ⟧ }

instance
  Hℕᵉ : Exp has ℕ
  Hℕᵉ .collect = nums𝔼 ∘ E

  Hℕᵉˢ : Exps has ℕ
  Hℕᵉˢ .collect = nums𝔼 ∘ ES

  Hℕᵛᵉˢ : VExps has ℕ
  Hℕᵛᵉˢ .collect = nums𝔼 ∘ VES

nums : ∀ {A : Set} ⦃ _ : A has ℕ ⦄ → A → List ℕ
nums = collect

private
  _ : nums (single (1 , "" , mkX 2 , ""))
   ++ nums (vsplit [ (tt , [ single (3 , "" , mkX 4 , "") ]) ])
   ++ nums [ (single (5 , "" , mkX 6 , "")) ]
   ++ nums [ (tt , [ single (7 , "" , mkX 8 , "") ]) ]
    ≡ ⟦ 1 , 2 , 3 , 4 , 5 , 6 , 7 , 8 ⟧
  _ = refl

-- names

Name = String ⊎ String

names𝔼 : 𝔼 → List Name
names𝔼 = mkCollect λ{ (_ , l , _ , r) → ⟦ inj₁ l , inj₂ r ⟧ }

instance
  HNᵉ : Exp has Name
  HNᵉ .collect = names𝔼 ∘ E

  HNᵉˢ : Exps has Name
  HNᵉˢ .collect = names𝔼 ∘ ES

  HNᵛᵉˢ : VExps has Name
  HNᵛᵉˢ .collect = names𝔼 ∘ VES

names : ∀ {A : Set} ⦃ _ : A has Name ⦄ → A → List Name
names = collect

private
  _ : names (single (1 , "a" , mkX 2 , "b"))
   ++ names (vsplit [ (tt , [ single (3 , "c" , mkX 4 , "d") ]) ])
   ++ names [ (single (5 , "e" , mkX 6 , "f")) ]
   ++ names [ (tt , [ single (7 , "g" , mkX 8 , "h") ]) ]
    ≡ ⟦ inj₁ "a" , inj₂ "b" , inj₁ "c" , inj₂ "d" , inj₁ "e" , inj₂ "f" , inj₁ "g" , inj₂ "h" ⟧
  _ = refl

-- subterms

subterms𝔼 : 𝔼 → Exps
subterms𝔼 (E e) = e ∷ (case e of λ where
  (single _)   → []
  (split es)   → subterms𝔼 (ES es)
  (vsplit ves) → subterms𝔼 (VES ves))
subterms𝔼 (ES []) = []
subterms𝔼 (ES (e ∷ es)) = subterms𝔼 (E e) ++ subterms𝔼 (ES es)
subterms𝔼 (VES []) = []
subterms𝔼 (VES ((_ , es) ∷ ves)) = subterms𝔼 (ES es) ++ subterms𝔼 (VES ves)

instance
  HSᵉ : Exp has Exp
  HSᵉ .collect = subterms𝔼 ∘ E

  HSᵉˢ : Exps has Exp
  HSᵉˢ .collect = subterms𝔼 ∘ ES

  HSᵛᵉˢ : VExps has Exp
  HSᵛᵉˢ .collect = subterms𝔼 ∘ VES

subterms : ∀ {A : Set} ⦃ _ : A has Exp ⦄ → A → Exps
subterms = collect

private
  _ : subterms (vsplit [ (tt , [ single (3 , "" , mkX 4 , "") ])])
    ≡ ⟦ vsplit [ (tt , [ single (3 , "" , mkX 4 , "") ])]
      , single (3 , "" , mkX 4 , "") ⟧
  _ = refl

-----------------------------
-- ** Lemmas

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
