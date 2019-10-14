module Dyck where


-- | Empty | = 0
data Empty : Set where

-- | Unit | = 1
data Unit : Set where

  -----------
  tt : Unit

-- | Bool | = 2
data Bool : Set where

  ------------
  true  : Bool

  ------------
  false : Bool

-- | Tri | = 3
data Tri : Set where

  ------------
  one  : Tri

  ------------
  two : Tri


  ------------
  three  : Tri

-- | A × B | = | A | * | B |
data _×_ (A : Set) (B : Set) : Set where

  _,_ :

      A
    → B
      -------
    → (A × B)

-- | A + B | = | A | + | B |
data _⊎_ (A : Set) (B : Set) : Set where


  left :

      A
      ------
    → A ⊎ B

  right :

      B
      ------
    → A ⊎ B


data _≡_ {A : Set} : A → A → Set where
  refl : ∀ {x : A}

       -------
     → x ≡ x

absurd : ∀ {ℓ} {A : Set ℓ} → Empty → A
absurd ()

bullshit : true ≡ false
bullshit = absurd impossible
  where postulate impossible : Empty

-- e.g. f : Empty → D³⁰
-- f emptyValue = ?


-- e.g. f : Tri → Bool
{- f one   = true
   f two   = true
   f three = true
   .
   .
   .
   fₙ one = false
   fₙ two   = false
   fₙ three = false
-}
-- | A → B | = | B | ̂ | A |

-- Constructors as coproducts
-- | Tri | = Unit + Unit + Unit = 1 + 1 + 1 = 3

-- Arguments as products
data Person : Set where
  mkPerson : Bool -- is gay??
           → Bool -- has boyfriend?
           → Tri  -- gender (M/F/Non-binary)
           → Person

-- | Person | ≃ | Bool × Bool × Tri | = 2 * 2 * 3 = 12

-- | ℕ | = | Z | + | S |
-- N ≃ Unit × N
data ℕ : Set where

  Z : ℕ

  S : ℕ → ℕ

{- | T | = | Z | + | S |
         = 1     + | T |
         = 1     + 1 + |T|
         .
         .
         .
         = 1 + 1 + 1 + ...

-}

open import Data.Product using (_×_; _,_; Σ; Σ-syntax)
-- open import Data.String  using (String; length)
----------------------- D² --------------------------

{- ** Grammar **

S → ε
  | ( S ) S

-- we say, a word is recognized by S (w ∈ S)

-}

{- ** Datatype ** -}
data T : Set where

  Leaf : ℕ → T

  Node : T → T → T


{-
-- we say, a tree is a value of type T (t ∈ T)

{-

T² = (a + T²)² = a² + 2aT² + T⁴
T⁴ = a⁴ + 4a³T² + 6a²T⁴ + 4aT⁶ + T⁸

⟦ T ⟧ = ⟦ Leaf ⟧ + ⟦ Node ⟧
      = a + ⟦ T ⟧²
      = a + (a + T²)²
      = a + a² + 2aT² + T⁴
      = a + a² + 2a(a² + 2aT² + T⁴) + T⁴
      = a + a² + (2a³ + 4a²T² + T⁴) + T⁴
      = a + a² + 2a³ + 4a²(a² + 2aT² + T⁴) + T⁴ + T⁴
      .
      .
      .
      = a + a² + 2a³ + 5a⁴ + ....
      ≈ 1 , 1  , 2   , 5  , 14 , 42 , 132 , 429 , ... ≡ D²
-}


----------------------- D³ --------------------------

open import Function using (_$_; _∋_)
import Data.Vec as V
open import Data.List using (List; []; _∷_; [_]; length; concat)
open import Data.List.Relation.Ternary.Interleaving.Propositional as I using (Interleaving; _∷ˡ_; _∷ʳ_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

data Symbol : Set where
  a : Symbol
  b : Symbol
  c : Symbol

String : Set
String = List Symbol

data Word : Set where
  ∣_∣_∣_∣ : String → String → String → Word

Strings : Set
Strings = List String

toStrings : Word → Strings
toStrings ∣ x ∣ y ∣ z ∣ = x ∷ y ∷ z ∷ []

_↔_≈_ : Word → Word → Strings → Set
w₁ ↔ w₂ ≈ ws = Interleaving (toStrings w₁) (toStrings w₂) ws


infix 1 _-splitsTo-_
data _-splitsTo-_ : String → Word → Set where

  base : [] -splitsTo- ∣ [] ∣ [] ∣ [] ∣


  base₁ : ∀ {x} → [ x ] -splitsTo- ∣ [] ∣ [] ∣ [ x ] ∣

  step₁ : ∀ {x xs xs′}

    → xs -splitsTo- ∣ [] ∣ [] ∣ xs′ ∣
      -------------------------------------
    → x ∷ xs -splitsTo- ∣ [] ∣ [] ∣ x ∷ xs′ ∣

  step₁′ : ∀ {x xs xs′}

    → xs -splitsTo- ∣ [] ∣ [] ∣ xs′ ∣
      -------------------------------------
    → x ∷ xs -splitsTo- ∣ [] ∣ [ x ] ∣ xs′ ∣

  step₁″ : ∀ {x xs xs′}

    → xs -splitsTo- ∣ [] ∣ [] ∣ xs′ ∣
      -------------------------------------
    → x ∷ xs -splitsTo- ∣ [ x ] ∣ [] ∣ xs′ ∣

  step₂ : ∀ {x xs xs′ xs″}

    → xs -splitsTo- ∣ [] ∣ xs′ ∣ xs″ ∣
      -------------------------------------
    → x ∷ xs -splitsTo- ∣ [] ∣ x ∷ xs′ ∣ xs″ ∣

  step₂′ : ∀ {x xs xs′ xs″}

    → xs -splitsTo- ∣ [] ∣ xs′ ∣ xs″ ∣
      -------------------------------------
    → x ∷ xs -splitsTo- ∣ [ x ] ∣ xs′ ∣ xs″ ∣

  step₃ : ∀ {x xs xs′ xs″ xs‴}

    → xs -splitsTo- ∣ xs′ ∣ xs″ ∣ xs‴ ∣
      -------------------------------------
    → x ∷ xs -splitsTo- ∣ x ∷ xs′ ∣ xs″ ∣ xs‴ ∣


data Prograph : Word → Set where

  base : Prograph ∣ [ a ] ∣ [ b ] ∣ [ c ] ∣


  _⊗_⊢_ : ∀ {w₁ w₂ ws w}

    → Prograph w₁
    → Prograph w₂
    → (w₁ ↔ w₂ ≈ ws)
    × (concat ws -splitsTo- w)
      -----------------------
    → Prograph w


abc : Word
abc = ∣ [ a ] ∣ [ b ] ∣ [ c ] ∣

p-abc : Prograph abc
p-abc = base

aabbcc : Word
aabbcc = ∣ a ∷ [ a ] ∣ b ∷ [ b ] ∣ c ∷ [ c ] ∣

p-aabbcc : Prograph aabbcc
p-aabbcc = p-abc
         ⊗ p-abc
         ⊢ ( (refl ∷ˡ (refl ∷ʳ (refl ∷ˡ (refl ∷ʳ (refl ∷ˡ (refl ∷ʳ I.[]))))))
           , step₃ (step₂′ (step₂ (step₁′ (step₁ base₁))))
           )

-- Dummy inductive definition using two sub-dyck³
-- data Dyck : String3 → Set where

--   base : Dyck ("a" , "b" , c")

--   step : ∀ {x y z k l m : String}
--        → Dyck (x , y , z) -- n - 1
--        → Dyck (k , l , m) -- n - 1
--        → (x , y , z) ⊕ (k , l , m) ≡ w′ --
--        → Dyck w′ -- n


-- _⊕_≡_ : String3 → String3 → String3 → Set
-- _⊕_≡_ = ?

-}
-- Dummy inductive definition using two sub-dyck²

-- count : T → String -- D²
-- count = ?

open import Data.String using (String)
-- String3 : Set
-- String3 = String × String × String

_⊕_≃_ : T → T → String → Set
_⊕_≃_ = {!!}

data Dyck : String → Set where

  step : ∀ {w : String}
       → (x : T)
       → (y : T)
       → x ⊕ y ≃ w
       → Dyck w



-- x = D³ₙ / (D²ₙ)²
