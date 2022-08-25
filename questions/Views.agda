module Views where

open import Prelude.Init hiding (_∷ʳ_)
open import Prelude.DecEq
open import Prelude.Decidable

open L.Mem
open L.Perm
open import Prelude.Lists.Mappings

H : ∀ {x y : ℕ} {xs ys : List ℕ}
  (xs↭ : xs ↭ y ∷ ys)
  (x∈ : x ∈ xs)
  (fys : ys ↦ ℕ)
  (fy : ℕ) →
  let f : xs ↦ ℕ
      f = permute-↦ (↭-sym xs↭) $ cons-↦ y fy fys
      -- f = cons-↦ y fy fys ∘ ∈-resp-↭ xs↭
  in
  --———————————————————————————————————————
  case ∈-resp-↭ xs↭ x∈ of λ where
    (here refl) → f x∈ ≡ fy
    (there y∈)  → f x∈ ≡ fys y∈
H {x}{y}{xs}{ys} xs↭ x∈ fys fy
  with ∈-resp-↭ xs↭ x∈ in eq
... | here refl rewrite ↭-sym-involutive xs↭ | eq = refl
... | there y∈  rewrite ↭-sym-involutive xs↭ | eq = refl


{-
variable n n′ : ℕ

mutual
  -- infixr 4 _∷_
  data Consℕ : Set where
    _∙ : ∀ n {_ : True ¿ n ≡ 0 ¿} → Consℕ
    _∷_ : ∀ n (ns : Consℕ) {_ : True ¿ n ≡ suc (top ns) ¿} → Consℕ

  top : Consℕ → ℕ
  top (n ∙)   = n
  top (n ∷ _) = n

  data _∈ᶜ_ : ℕ → Consℕ → Set where
    _∙ : ∀ n {ns} → n ∈ᶜ (n ∷ ns)
    _∷_ : ∀ n ∈ ns → n ∈ᶜ (n′ ∷ ns)
  -- n ∈ᶜ ns = case ns of λ where
  --   (_ ∙) → n ≡ 0
  --   (n′ ∷ ns) → ⊎ n ∈

_ : Consℕ
_ = 5 ∷ 4 ∷ 3 ∷ 2 ∷ 1 ∷ 0 ∙

mutual
  infixl 4 _∷ʳ_
  data Snocℕ : Set where
    ∙_ : ℕ → Snocℕ
    _∷ʳ_ : ∀ (ns : Snocℕ) n {_ : True ¿ n ≡ Nat.pred (bottom ns) ¿} → Snocℕ

  bottom : Snocℕ → ℕ
  bottom (∙ n)    = n
  bottom (_ ∷ʳ n) = n

_ : Snocℕ
_ = ∙ 5 ∷ʳ 4 ∷ʳ 3 ∷ʳ 2 ∷ʳ 1 ∷ʳ 0

lemma : ∀ (xs : Consℕ)
  → top xs ≡ 5
    --———————
  → 0 ∈ᶜ xs
lemma xs top≡ = {!!}
-}



{-
-- * 1. un-viewed recursive arguments
data SnocList (A : Set ℓ) : Set ℓ where
  [] : SnocList A
  _∷_ : List A → A → SnocList A

private variable A : Set ℓ

mutual
  view : List A → SnocList A
  view [] = []
  view (x ∷ xs) with view xs
  ... | []     = [] ∷ x
  ... | ys ∷ y = (x ∷ ys) ∷ y

  unview : SnocList A → List A
  unview []        = []
  unview ([] ∷ x) = x ∷ []
  unview ((y ∷ ys) ∷ x) = x ∷ unview (ys ∷ x)

last : List A → Maybe A
last xs with view xs
... | []    = nothing
... | _ ∷ x = just x
-}

{-
-- * 2. viewed recursive arguments
data SnocList (A : Set ℓ) : Set ℓ where
  [] : SnocList A
  _∷_ : SnocList A → A → SnocList A

private variable A : Set ℓ

mutual
  -- NB. termination problems
  view : List A → SnocList A
  view [] = []
  view (x ∷ xs) with view xs
  ... | []     = [] ∷ x
  ... | ys ∷ y = view (x ∷ unview ys) ∷ y

  unview : SnocList A → List A
  unview []        = []
  unview (xs ∷ x) with unview xs
  ... | []     = x ∷ []
  ... | y ∷ ys = y ∷ unview (view ys ∷ x)

open import Prelude.Functor
open import Prelude.PointedFunctor
open import Prelude.Applicative
open import Prelude.Semigroup
open import Prelude.Nary

instance
  F-Snoc : Functor {ℓ} SnocList
  F-Snoc ._<$>_ _ [] = []
  F-Snoc ._<$>_ f (xs ∷ x) = (f <$> xs) ∷ f x

  PF-Snoc : PointedFunctor {ℓ} SnocList
  PF-Snoc .point = [] ∷_

  A-Snoc : Applicative {ℓ} SnocList
  A-Snoc .pure = point
  A-Snoc ._<*>_ fs as = view $ unview fs <*> unview as

  SG-Snoc : Semigroup (SnocList A)
  SG-Snoc ._◇_ xs ys = view $ unview xs ◇ unview ys

private
  _ : SnocList ℕ
  _ = ⟦ 1 , 2 , 3 ⟧

last : List A → Maybe A
last xs with view xs
... | []    = nothing
... | _ ∷ x = just x
-}

-- * 3. Indexed views
{-
private variable A : Set ℓ

data SnocList {A : Set ℓ} : Pred (List A) ℓ where
  [] : SnocList []
  _∷_ : (xs : List A) → (x : A) → SnocList (xs L.∷ʳ x)

mutual
  view : (xs : List A) → SnocList xs
  view [] = []
  view (x ∷ xs) with view xs
  ... | []     = [] ∷ x
  ... | ys ∷ y = (x ∷ ys) ∷ y

  unview : ∀ {xs : List A} → SnocList xs → List A
  unview {xs = xs} _ = xs

last : List A → Maybe A
last xs with view xs
... | []    = nothing
... | _ ∷ x = just x
-}

{-
-- * 4. Unifying typeclass (simply-typed)
private variable A : Set

record _▷_ (A B : Set) : Set where
  field
    view : A → B
    unview : B → A
    unview∘view : ∀ x → unview (view x) ≡ x
    view∘unview : ∀ y → view (unview y) ≡ y

open _▷_ ⦃ ... ⦄ public

view_as_ : A → (B : Set) ⦃ _ : A ▷ B ⦄ → B
view x as B = view {B = B} x

data SnocList (A : Set ℓ) : Set ℓ where
  [] : SnocList A
  _∷_ : SnocList A → A → SnocList A

instance
  SnocView : List A ▷ SnocList A
  {-# TERMINATING #-}
  SnocView .view = λ where
    [] → []
    (x ∷ xs) → case view xs of λ where
      [] → [] ∷ x
      (ys ∷ y) → view (x ∷ unview ys) ∷ y
  SnocView .unview = λ where
    [] → []
    (xs ∷ x) → case unview xs of λ where
      [] → x ∷ []
      (y ∷ ys) → y ∷ unview (view ys ∷ x)
  SnocView .unview∘view = λ where
    [] → refl
    (x ∷ xs) → {!!}
  SnocView .view∘unview = {!!}

last : List A → Maybe A
last {A = A} xs with view xs as SnocList A
... | []    = nothing
... | _ ∷ x = just x
-}

{-
-- * 5. Unifying typeclass (dependently-typed)
private variable A : Set

record _▷_ (A : Set) (P : Pred₀ A) : Set where
  field
    view : (x : A) → P x

  unview : ∀ {x} → P x → A
  unview {x = x} _ = x
open _▷_ ⦃ ... ⦄ public

view_as_ : (x : A) (P : Pred₀ A) ⦃ _ : A ▷ P ⦄ → P x
view x as P = view {P = P} x

data SnocList {A : Set} : Pred₀ (List A) where
  [] : SnocList []
  _∷_ : (xs : List A) → (x : A) → SnocList (xs L.∷ʳ x)

instance
  SnocView : List A ▷ SnocList
  SnocView .view = λ where
    [] → []
    (x ∷ xs) → case view xs of λ where
      [] → [] ∷ x
      (ys ∷ y) → (x ∷ ys) ∷ y

last : List A → Maybe A
last xs with view xs as SnocList
... | []    = nothing
... | _ ∷ x = just x

private
  open import Prelude.Nary
  _ : SnocList (List ℕ ∋ ⟦ 1 , 2 , 3 ⟧)
  _ = ⟦ 1 , 2 ⟧ ∷ 3
-}
