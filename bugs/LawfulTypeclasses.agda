open import Prelude.Init; open SetAsType

-- ** 1a. single level: no lawful wrappers
record Interface (A : Type) : Type where
  field method1 : A → ℕ; method2 : A → A → ℕ
open Interface ⦃...⦄ public

record Laws (A : Type) ⦃ _ : Interface A ⦄ : Type where
  field method-correct : ∀ (x y : A) → method2 x y ≡ method1 x + method1 y
open Laws ⦃...⦄ public

module 𝟙a {A : Type} ⦃ _ : Interface A ⦄ ⦃ _ : Laws A ⦄ where
  method3 : A → A → A → ℕ
  method3 x y z = method2 x y + method1 z

  method3-correct : ∀ x y z → method3 x y z ≡ method1 x + method1 y + method1 z
  method3-correct x y z rewrite method-correct x y = refl

-- ** 1b. single level: using lawful interface
record Lawful-Interface (A : Type) : Type where
  field ⦃ hasInterface ⦄ : Interface A
        ⦃ respectsLaws ⦄ : Laws A
open Lawful-Interface ⦃...⦄ using () public

module 𝟙b {A : Type} ⦃ _ : Lawful-Interface A ⦄ where
  method3 : A → A → A → ℕ
  method3 x y z = method2 x y + method1 z

  method3-correct : ∀ x y z → method3 x y z ≡ method1 x + method1 y + method1 z
  method3-correct x y z rewrite method-correct x y = refl

record Interface′ (A : Type) ⦃ _ : Interface A ⦄ : Type where
  field op : A → A
open Interface′ ⦃...⦄ public

record Laws′ (A : Type) ⦃ _ : Interface A ⦄ ⦃ _ : Laws A ⦄ ⦃ _ : Interface′ A ⦄ : Type where
-- record Laws′ (A : Type) ⦃ _ : Lawful-Interface A ⦄ ⦃ _ : Interface′ A ⦄ : Type where
  field op-correct : ∀ (x : A) → op (op x) ≡ op x
open Laws ⦃...⦄ public

-- ** 2a. two levels: no lawful wrapper
module 𝟚a {A : Type} ⦃ _ : Interface A ⦄ ⦃ _ : Laws A ⦄ ⦃ _ : Interface′ A ⦄ ⦃ _ : Laws′ A ⦄ where
    method3 : A → A → A → ℕ
    method3 x y z = method2 x y + method1 (op z)

    method3-correct : ∀ x y z → method3 x y z ≡ method1 x + method1 y + method1 (op z)
    method3-correct x y z rewrite method-correct x y = refl

-- record Lawful-Interface′ (A : Type) ⦃ _ : Lawful-Interface A ⦄ : Type where
-- -- record Lawful-Interface′ (A : Type) ⦃ _ : Interface A ⦄ ⦃ _ : Laws A ⦄ : Type where
--   field ⦃ hasInterface ⦄ : Interface′ A
--         ⦃ respectsLaws ⦄ : Laws′ A
-- open Lawful-Interface′ ⦃...⦄ using () public

-- -- ** 2b. two levels: only outer lawful wrapper
-- module 𝟚b {A : Type} ⦃ _ : Interface A ⦄ ⦃ _ : Laws A ⦄ ⦃ _ : Lawful-Interface′ A ⦄ where
--   method3 : A → A → A → ℕ
--   method3 x y z = method2 x y + method1 (op z)

-- --   method3-correct : ∀ x y z → method3 x y z ≡ method1 x + method1 y + method1 z
-- --   method3-correct x y z rewrite method-correct x y = refl

-- -- ** 2c. two levels: only inner lawful wrapper
-- module 𝟚c {A : Type} ⦃ _ : Lawful-Interface A ⦄ ⦃ _ : Interface′ A ⦄ ⦃ _ : Laws′ A ⦄ where
--   method3 : A → A → A → ℕ
--   method3 x y z = method2 x y + method1 (op z)

--   -- method3-correct : ∀ x y z → method3 x y z ≡ method1 x + method1 y + method1 z
--   -- method3-correct x y z rewrite method-correct x y = refl

-- -- ** 2d. two levels: both outer and inner lawful wrapper
-- module 𝟚d {A : Type} ⦃ _ : Lawful-Interface A ⦄ where
--   _ : Interface A
--   _ = it

--   _ : Laws A
--   _ = it

--   _ : Lawful-Interface A
--   _ = it

-- -- module 𝟚d {A : Type} ⦃ i : Lawful-Interface A ⦄ ⦃ _ : Lawful-Interface′ A ⦃ i ⦄ ⦄ where
-- --   method3 : A → A → A → ℕ
-- --   method3 x y z = method2 x y + method1 (op z)

--   -- method3-correct : ∀ x y z → method3 x y z ≡ method1 x + method1 y + method1 z
--   -- method3-correct x y z rewrite method-correct x y = refl
