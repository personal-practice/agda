-- ** using well-founded recursion
module RobustCollections where

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
-- ** Well-founded recursion

open import Induction using (Recursor)

data _≺_ : Rel 𝔼 0ℓ where
  [ES→E] : e ∈ es → E e ≺ ES es
  [VES→ES] : es ∈ map proj₂ ves → ES es ≺ VES ves
  instance
    [E→ES] : ES es ≺ E (split es)
    [E→VES] : VES ves ≺ E (vsplit ves)

≺-wf : WellFounded _≺_
≺-wf = acc ∘ _≻_
  where
    _≻_ : ∀ e e′ → e′ ≺ e → Acc _≺_ e′
    (.(E (split _)) ≻ .(ES _)) [E→ES] = acc (_ ≻_)
    (.(E (vsplit _)) ≻ .(VES _)) [E→VES] = acc (_ ≻_)

    (.(ES _) ≻ .(E _)) ([ES→E] (here refl)) = acc (_ ≻_)
    (.(ES _) ≻ .(E _)) ([ES→E] (there p)) = (_ ≻ _) ([ES→E] p)
    (.(VES _) ≻ .(ES _)) ([VES→ES] {ves = _ ∷ _} (here refl)) = acc (_ ≻_)
    (.(VES _) ≻ .(ES _)) ([VES→ES] {ves = _ ∷ _} (there p)) = (_ ≻ _) ([VES→ES] p)


≺-rec : Recursor (WF.WfRec _≺_)
≺-rec = WF.All.wfRec ≺-wf 0ℓ

-----------------------------
-- ** Collectors

mkCollect′ : ∀ {X : Set} → (∀ e → (∀ e′ → e′ ≺ E e → List X) → List X) → 𝔼 → List X
mkCollect′ {X = X} mk = ≺-rec _ go
  where
    go : ∀ e → (∀ e′ → e′ ≺ e → List X) → List X
    go (E e)     f = mk e f
    go (ES es)   f = concat $ mapWith∈ es (f (E _) ∘ [ES→E])
    go (VES ves) f = concat $ mapWith∈ (map proj₂ ves) (f (ES _) ∘ [VES→ES])

mkCollect : ∀ {X : Set} → (Payload → List X) → 𝔼 → List X
mkCollect {X = X} mk = mkCollect′ go
  where
    go : ∀ e → (∀ e′ → e′ ≺ E e → List X) → List X
    go (single s)   _ = mk s
    go (split es)   f = f (ES es) it
    go (vsplit ves) f = f (VES ves) it

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
subterms𝔼 = mkCollect′ λ e f → e ∷ go e f
  where
    go : ∀ e → (∀ e′ → e′ ≺ E e → Exps) → Exps
    go (single _) _   = []
    go (split es) f   = f (ES es) it
    go (vsplit ves) f = f (VES ves) it

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
