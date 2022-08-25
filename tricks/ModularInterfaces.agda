module ModularInterfaces where

open import Prelude.Init hiding (module F)

module Interface where
  record F (A : Set) : Set where
    field get : A → ℕ
    get∗ : List A → ℕ
    get∗ = sum ∘ map get
  open F ⦃...⦄

  record ValidF (A : Set) ⦃ super : F A ⦄ : Set where
    field get-+ : ∀ {a : A} → get a + get∗ [ a ] ≡ 2 * get a

  record G (A : Set) ⦃ super : F A ⦄ : Set where
    field put : ℕ → A → A
    put∗ : List ℕ → A → A
    put∗ = flip $ foldl (flip put)
  open G ⦃...⦄

  record ValidFG (A : Set) ⦃ superF : F A ⦄ ⦃ superG : G A ⦄ : Set where
    field put∘get : ∀ {a : A} → put (get a) a ≡ a

  record H (A : Set) ⦃ super : F A ⦄ : Set where
    field print : String → A → A

  record ImplementF (A : Set) : Set where
    field f : F A
    instance _ = F A ∋ f
    field g : G A; h : H A
    open F f public; open G g public; open H h public

open import Prelude.Bifunctor
module Implementation where
  abstract
    X : Set
    X = String × ℕ
    variable x : X

    get : X → ℕ
    get = proj₂

  get∗ : List X → ℕ
  get∗ = sum ∘ map get

  -- open import Prelude.Tactics
  -- unquoteDecl get∗ = default get∗ ↜ Interface.F.get∗

  abstract
    get-+ : ∀ {a : X} → get a + get∗ [ a ] ≡ 2 * get a
    get-+ {_ , n} rewrite Nat.+-identityʳ n = refl

    put : ℕ → X → X
    put = map₂ ∘ const

    put∘get : put (get x) x ≡ x
    put∘get = refl

    print : String → X → X
    print _ = id

module UserLand where
  open Interface
  module Imp = Implementation

  open ImplementF record
    { f = record {Imp}
    ; g = record {Imp}
    ; h = record {Imp}
    } public

--   fa = F _ ∋ record {Imp}
--   open F fa public
--   open ValidF ⦃ fa ⦄ record {Imp} public
--   ga = G _ ⦃ fa ⦄ ∋ record {Imp}
--   open G ⦃ fa ⦄ ga public
--   open ValidFG ⦃ fa ⦄ ⦃ ga ⦄ record {Imp} public
--   open H ⦃ fa ⦄ record {Imp} public
