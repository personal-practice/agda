module FinWellFounded where

open import Prelude.Init
open import Prelude.Ord
open import Prelude.General

private variable
  n m n′ m′ : ℕ
  fn : Fin n
  fn′ : Fin n′
  fm : Fin m
  fm′ : Fin m′

<-wf : WellFounded _<_
<-wf n = acc $ go n
  where
    go : ∀ n m → m < n → Acc _<_ m
    go (suc n) zero    m<n       = acc λ _ ()
    go (suc n) (suc m) (s≤s m<n) = acc λ o o<sm → go n o (Nat.<-transˡ o<sm m<n)

-- _≺_ : Fin n → Fin m → Set
-- _≺_ {n}{m} _ _ = n < m

-- [IMPOSSIBLE] WellFounded is a homogeneous relation (i.e. can only relate Fin n ↔ Fin n)
-- ≺-wf : WellFounded _≺_
-- ≺-wf n = ?


-- [IMPOSSIBLE] Cannot define accessibility on heterogeneous relation, as it breaks recursion
-- module _ {a b} {A : Set a} {B : Set b} where

--   open import Relation.Binary.Core using (REL)

--   data Acc′ (_<_ : REL A B ℓ) (x : A) : Set (a ⊔ₗ ℓ) where
--     acc :
--       (∀ y → y < x → Acc _<_ y)
--       ────────────────────────────
--       Acc _<_ x

--   WellFounded′ : REL A B ℓ → Set _
--   WellFounded′ _<_ = ∀ x → Acc′ _<_ x


-- module _ {ℙ ℚ : Pred ℕ} where
--   variable x y : ℕ
--   _≺_ : ℙ x → ℚ y → Set
--   _≺_ {x}{y} _ _ = x < y

module Ex₁ where
  ℙ : Pred₀ ℕ
  ℙ = Fin

  ℚ : ∀ {x} → ℙ x → Set
  ℚ fn = fn ≡ fn

  postulate
    fhalf : Fin n → Fin Nat.⌊ n /2⌋
    ℚ↑ : ∀ {fn : Fin n} → ℚ (fhalf fn) → ℚ fn
    /2-less : ∀ n → Nat.⌊ n /2⌋ < n

  f : (p : ℙ n) → ℚ p
  f {n} = go _ (<-wf n)
    where
      go : ∀ n → Acc _<_ n
        → (p : ℙ n)
        → ℚ p
      go _ (acc _)   0F          = refl
      go _ (acc rec) fn@(fsuc _) = ℚ↑ $ go _ (rec _ (/2-less _)) (fhalf fn)

module Ex₂ where
  postulate
    A : Set
    toN : A → ℕ

  ℚ : Pred₀ A
  ℚ x = x ≡ x

  postulate
    fhalf : A → A
    ℚ↑ : ∀ {x : A} → ℚ (fhalf x) → ℚ x
    /2-less : ∀ n → Nat.⌊ n /2⌋ < n

  f : (x : A) → ℚ x
  f x = go _ (<-wf $ toN x) x
    where
      go : ∀ n → Acc _<_ n
        → (x : A)
        → ℚ x
      go _ (acc rec) x = ℚ↑ $ go _ (rec _ (/2-less _)) (fhalf x)

module Ex₃ where
  variable s w : String
  postulate
    A : String → Set
    toN : A s → ℕ

  ℚ : Pred₀ (A s)
  ℚ x = x ≡ x

  open import Prelude.Semigroup
  postulate
    fhalf : A s → A (s ◇ "'")
    ℚ↑ : ∀ {a : A s} → ℚ (fhalf a) → ℚ a
    /2-less : ∀ n → Nat.⌊ n /2⌋ < n

  f : (x : A s) → ℚ x
  f x = go _ (<-wf $ toN x) x
    where
      go : ∀ n → Acc _<_ n
        → (x : A s)
        → ℚ x
      go _ (acc rec) x = ℚ↑ $ go _ (rec _ (/2-less _)) (fhalf x)

module Ex₄ where
  open import Prelude.Semigroup
  open import Prelude.Measurable
  variable s w : String
  postulate
    A : String → Set
    toN : A s → ℕ

  instance
    M-A : Measurable (A s)
    M-A .∣_∣ = toN

  ℚ : Pred₀ (A s)
  ℚ x = x ≡ x

  postulate
    fhalf : A s → A (s ◇ "'")
    /2-less : ∀ n → Nat.⌊ n /2⌋ < n
    fhalf≡ : ∀ {a : A s} → ∣ fhalf a ∣ ≡ Nat.⌊ ∣ a ∣ /2⌋
    ℚ↑ : ∀ {a : A s} → ℚ (fhalf a) → ℚ a

  f : (x : A s) → ℚ x
  f x = go _ (<-wf ∣ x ∣) x refl
    where
      go : ∀ n → Acc _<_ n
        → (x : A s)
        → ∣ x ∣ ≡ n
        → ℚ x
      go _ (acc rec) x refl = ℚ↑ $ go _ (rec _ (/2-less _)) (fhalf x) fhalf≡

module Ex₅ where
  open import Prelude.Semigroup
  open import Prelude.Measurable
  variable s w : String
  postulate
    A : String → Set
    toN : A s → ℕ

  instance
    M-A : Measurable (A s)
    M-A .∣_∣ = toN

  ℚ : Pred₀ (A s)
  ℚ x = x ≡ x

  postulate
    fhalf : A s → A (s ◇ "'")
    /2-less : ∀ n → Nat.⌊ n /2⌋ < n
    fhalf≡ : ∀ {a : A s} → ∣ fhalf a ∣ ≡ Nat.⌊ ∣ a ∣ /2⌋
    ℚ↑ : ∀ {a : A s} → ℚ (fhalf a) → ℚ a

  f : (x : A s) → ℚ x
  f x = go _ (≺-wf ∣ x ∣) x refl
    where
      go : ∀ n → Acc _<_ n
        → (x : A s)
        → ∣ x ∣ ≡ n
        → ℚ x
      go _ (acc rec) x refl = ℚ↑ $ go _ (rec _ (/2-less _)) (fhalf x) fhalf≡




















-- f : Fin n → Fin Nat.⌊ n /2⌋
-- f {n} fn = go _ (<-wf n) fn
--   where
--     go : ∀ n → Acc _<_ n → Fin n → Fin Nat.⌊ n /2⌋
--     go (suc zero) (acc rec) 0F = {!!}
--     go (suc (suc n)) (acc rec) 0F = 0F
--     go (suc (suc n)) (acc rec) 1F = {!!}
--     go (suc (suc n)) (acc rec) (fsuc (fsuc fn)) = fsuc $ go n (rec _ {!!}) fn
    -- fsuc $ go n (rec _ (s≤s {!!})) {!fn!}

-- -- _≺′_ : ∃ Fin → ∃ Fin → Set
-- -- _≺′_ = _<_ on proj₁

-- -- -- ≺′-wf : WellFounded _≺′_
-- -- -- ≺′-wf n = acc $ go n
-- -- --   where
-- -- --     go : ∀ fn fm → fm ≺′ fn → Acc _≺′_ fm
-- -- --     go fn@(suc n , _) fm@(0     , _) m≺n       = acc λ _ ()
-- -- --     go fn@(suc n , _) fm@(suc m , _) (s≤s m≺n) = acc λ o o≺sm → go fn o (Nat.<-transˡ o≺sm m≺n)


-- -- f : Fin n → Fin Nat.⌊ n /2⌋
-- -- f {n} fn = go _ (<-wf n) fn
-- --   where
-- --     go : ∀ n → Acc _<_ n → Fin n → Fin Nat.⌊ n /2⌋
-- --     go (suc zero) (acc rec) 0F = {!!}
-- --     go (suc (suc n)) (acc rec) 0F = 0F
-- --     go (suc (suc n)) (acc rec) 1F = {!!}
-- --     go (suc (suc n)) (acc rec) (fsuc (fsuc fn)) = fsuc $ go n (rec _ {!!}) fn
-- --     -- fsuc $ go n (rec _ (s≤s {!!})) {!fn!}


-- -- -- -- <-rec′ = All.wfRec <-wf 0ℓ
-- -- -- -- ≈ Data.Nat.Induction.<-rec

-- -- -- -- f′ : ℕ → ℕ
-- -- -- -- f′ = <-rec′ _ go
-- -- -- --   where
-- -- -- --     go : ∀ n → (∀ m → m < n → ℕ) → ℕ
-- -- -- --     go zero    _ = 0
-- -- -- --     go (suc n) r = r ⌊ n /2⌋ (s≤s $ /2-less _)
