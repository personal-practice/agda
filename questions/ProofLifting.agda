open import Prelude.Init
open Fun.Inv using (_InverseOf_) -- ; open Inverse
-- open Fun.Eq; open Π using (_⟨$⟩_)
open Fun.Eq.Π using (_⟨$⟩_)
open SetAsType
open import Prelude.Ord
open import Prelude.Decidable
open import Prelude.Setoid

itω : ∀ {A : Setω} → ⦃ A ⦄ → A
itω ⦃ x ⦄ = x

record _≃_ (A : Type ℓ) (B : Type ℓ′) ⦃ la : Lawful-Setoid A ⦄ ⦃ lb : Lawful-Setoid B ⦄
  : Type (ℓ ⊔ₗ ℓ′ ⊔ₗ relℓ {A = A} ⊔ₗ relℓ {A = B}) where
  field
    to≃        : (A ⟶ B) ⦃ la ⦄ ⦃ lb ⦄
    from≃      : (B ⟶ A) ⦃ lb ⦄ ⦃ la ⦄
    inverse-of : from≃ InverseOf to≃

  to : A → B
  to  = to≃ ⟨$⟩_

  from : B → A
  from = from≃ ⟨$⟩_
open _≃_ ⦃...⦄ public

variable
  n : ℕ
  A B : Type
  P : Pred₀ A
  X : Type ℓ

-- data Vec (A : Type) : ℕ → Type where
--   [] : Vec A 0
--   _∷_ : A → Vec A n → Vec A (suc n)

FVec : Type → ℕ → Type
FVec A n = Fin n → A

mkSetoid≡ : ISetoid X
mkSetoid≡ = λ where
  .relℓ → _
  ._≈_  → _≡_

mkSetoidLaws≡ : Setoid-Laws X ⦃ mkSetoid≡ ⦄
mkSetoidLaws≡ .isEquivalence = PropEq.isEquivalence

mkSetoid→ : ISetoid (A → B)
mkSetoid→ = λ where
  .relℓ → _
  ._≈_  → _≗_

mkSetoidLaws→ : Setoid-Laws (A → B) ⦃ mkSetoid→ ⦄
mkSetoidLaws→ .isEquivalence = Setoid.isEquivalence (_ PropEq.→-setoid _)

instance
  Setoid-Vec : ISetoid (Vec A n)
  Setoid-Vec = mkSetoid≡

  SetoidLaws-Vec : Setoid-Laws (Vec A n)
  SetoidLaws-Vec = mkSetoidLaws≡

  Setoid-Fin : ISetoid (Fin n)
  Setoid-Fin = mkSetoid≡

  SetoidLaws-Fin : Setoid-Laws (Fin n)
  SetoidLaws-Fin = mkSetoidLaws≡

  Setoid-FVec : ISetoid (FVec A n)
  Setoid-FVec = mkSetoid→

  SetoidLaws-FVec : Setoid-Laws (FVec A n)
  SetoidLaws-FVec = mkSetoidLaws→

instance
  F≃V : FVec A n ≃ Vec A n
  F≃V = λ where
    .to≃   → record {_⟨$⟩_ = V.tabulate; cong = V.tabulate-cong}
    .from≃ → record {_⟨$⟩_ = V.lookup;   cong = λ where refl → λ _ → refl}
    .inverse-of → record {left-inverse-of = V.lookup∘tabulate; right-inverse-of = V.tabulate∘lookup}

open V.All using (_∷_; [])
VAll = V.All.All

FAll : Pred₀ A → Pred₀ (FVec A n)
FAll P fv = ∀ fn → P (fv fn)

-- ↑_ : ∀ {v : Vec A n} {fv : FVec A n} → from v ≈ fv → VAll P v → FAll P fv
-- ↑_ {A = A}{n} {P = P} {v = v@(x ∷ xs)} {fv = fv} eq (px ∷ pxs) = λ where
--   fzero    → let record {cong = c} = to≃ ⦃ r = F≃V {A = A} {n = n} ⦄ in subst P (sym {!!}) px
--   (fsuc n) → {!↑_ ? pxs!}

tooo : ∀ {v : Vec A n} {fv : FVec A n}
  → from v ≗ fv
  → VAll P v → FAll P fv
tooo {P = P} eq vp = λ n → subst P (eq n) $ V.All.lookup n vp

frooo : ∀ {v : Vec A n} {fv : FVec A n}
  → from v ≗ fv
  → FAll P fv → VAll P v
frooo {P = P} eq fp = V.All.tabulate λ n → subst P (sym $ eq n) (fp n)

instance

  Setoid-VAll : {v : Vec A n} → ISetoid (VAll P v)
  Setoid-VAll = mkSetoid≡

  SetoidLaws-VAll : {v : Vec A n} → Setoid-Laws (VAll P v)
  SetoidLaws-VAll = mkSetoidLaws≡

  Setoid-FAll : {fv : FVec A n} → ISetoid (FAll P fv)
  Setoid-FAll = λ where
    .relℓ → 0ℓ
    ._≈_  p q → ∀ (n : Fin _) → p n ≡ q n

  SetoidLaws-FAll : {fv : FVec A n} → Setoid-Laws (FAll P fv)
  SetoidLaws-FAll = {!!}


  PF≃PV : ∀ {v : Vec A n} {fv : FVec A n}
    → FAll P fv ≃ VAll P v
  PF≃PV = λ where
    .to≃   → {!frooo ?!} -- record {_⟨$⟩_ = V.tabulate; cong = V.tabulate-cong}
    .from≃ → {!!} -- record {_⟨$⟩_ = V.lookup;   cong = λ where refl → λ _ → refl}
    .inverse-of → {!!} -- record {left-inverse-of = V.lookup∘tabulate; right-inverse-of = V.tabulate∘lookup}

private
  v : Vec ℕ 3
  v  = 5 ∷ 6 ∷ 7 ∷ []

  fv : FVec ℕ 3
  fv = λ where
    0F → 5
    1F → 6
    2F → 7

  _ : to fv ≡ v
  _ = refl

  _ : from v ≗ fv
  _ = λ where
    0F → refl
    1F → refl
    2F → refl

  p : Pred₀ ℕ
  p = _≥ 5

  pv : VAll p v
  pv = auto ∷ auto ∷ auto ∷ []

  pfv : FAll p fv
  pfv = λ where
    0F → auto
    1F → auto
    2F → auto

  too : VAll p v → FAll p fv
  too (p ∷ q ∷ r ∷ []) = λ where
    0F → p
    1F → q
    2F → r

  froo : FAll p fv → VAll p v
  froo fp = fp 0F ∷ fp 1F ∷ fp 2F ∷ []
