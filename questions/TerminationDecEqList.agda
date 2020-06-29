{-# OPTIONS -v Prelude.Generics:10 #-}
{-# OPTIONS --postfix-projections #-}

module TerminationDecEqList where

open import Level using (0ℓ)
open import Function using (_∘_; _$_; case_of_; _∋_)
open import Reflection hiding (_≟_)
open import Reflection.TypeChecking.MonadSyntax using (pure; _<*>_; _<$>_; _>>_) -- for idiom brackets to work
open import Reflection.Argument as RArg using (unArg)
open import Reflection.Name
  renaming (_≟_ to _≟ₙ_)
open import Reflection.Term
  renaming (_≟_ to _≟ₜ_)

open import Data.Unit
  renaming (_≟_ to _≟⊤_)
open import Data.Product
  hiding (map)
open import Data.Product.Properties
  renaming (≡-dec to _≟×_)
open import Data.Sum
  hiding (map; map₁; map₂; [_,_])
open import Data.Sum.Properties
  renaming (≡-dec to _≟⊎_)
open import Data.Bool
  renaming (_≟_ to _≟𝔹_)
open import Data.Maybe
  using (Maybe; just; nothing)
import Data.Maybe.Properties as MaybeP
open import Data.Nat
  renaming (_≟_ to _≟ℕ_)
import Data.Nat.Show as Showℕ
open import Data.Integer
  using (ℤ)
  renaming (_≟_ to _≟ℤ_)
open import Data.String
  using (String; intersperse; parens)
  renaming (_≟_ to _≟s_; _++_ to _<>_)
open import Data.List
  hiding (intersperse; lookup)
import Data.List.Properties as ListP
open import Data.Vec using (Vec)
import Data.Vec.Properties as VecP

open import Data.Fin using (Fin; toℕ)
  renaming (_≟_ to _≟Fin_)

open import Relation.Nullary using (yes; no; _because_; ofʸ; ofⁿ)
open import Relation.Nullary.Decidable.Core using (⌊_⌋)
open import Relation.Binary using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Prelude.Generics
open import Prelude.Generics using (DERIVE) public
open import Prelude.Lists hiding (⟦_⟧)
open import Prelude.Show

private
  variable
    A B : Set

record DecEq (A : Set) : Set where
  field
    _≟_ : Decidable {A = A} _≡_

  _==_ : A → A → Bool
  x == y = ⌊ x ≟ y ⌋

  _≠_ : A → A → Bool
  x ≠ y = not (x == y)

  infix 4 _≟_ _==_ _≠_

open DecEq {{...}} public

instance
  DecEq-⊤ : DecEq ⊤
  DecEq-⊤ ._≟_ = _≟⊤_

  DecEq-Σ : ∀ {B : A → Set} {{_ : DecEq A}} {{_ : ∀ {x} → DecEq (B x)}} → DecEq (Σ A B)
  DecEq-Σ ._≟_ (x , y) (x′ , y′)
    with x ≟ x′
  ... | no ¬p    = no λ{ refl → ¬p refl }
  ... | yes refl
    with y ≟ y′
  ... | no ¬p    = no λ{ refl → ¬p refl }
  ... | yes refl = yes refl

  DecEq-⊎ : {{_ : DecEq A}} {{_ : DecEq B}} → DecEq (A ⊎ B)
  DecEq-⊎ ._≟_ = _≟_ ≟⊎ _≟_

  DecEq-Bool : DecEq Bool
  DecEq-Bool ._≟_ = _≟𝔹_

  DecEq-ℕ : DecEq ℕ
  DecEq-ℕ ._≟_ = _≟ℕ_

  DecEq-ℤ : DecEq ℤ
  DecEq-ℤ ._≟_ = _≟ℤ_

  DecEq-Fin : ∀ {n} → DecEq (Fin n)
  DecEq-Fin ._≟_ = _≟Fin_

  DecEq-String : DecEq String
  DecEq-String ._≟_ = _≟s_

  DecEq-List : {{_ : DecEq A}} → DecEq (List A)
  -- DecEq-List ._≟_ = ListP.≡-dec _≟_
  DecEq-List {A = A} ._≟_ = _≡?_
    where
      _≡?_ : Decidable {A = List A} _≡_
      [] ≡? []      = yes refl
      [] ≡? (_ ∷ _) = no λ()
      (_ ∷ _) ≡? [] = no λ()
      (x ∷ xs) ≡? (y ∷ ys) with x ≟ y
      ... | no ¬p    = no λ{ refl → ¬p refl }
      ... | yes refl with xs ≡? ys
      ... | no ¬p    = no λ{ refl → ¬p refl }
      ... | yes refl = yes refl

  -- DecEq-List ._≟_ [] []      = yes refl
  -- DecEq-List ._≟_ [] (_ ∷ _) = no λ()
  -- DecEq-List ._≟_ (_ ∷ _) [] = no λ()
  -- DecEq-List ._≟_ (x ∷ xs) (y ∷ ys) with x ≟ y
  -- ... | no ¬p    = no λ{ refl → ¬p refl }
  -- ... | yes refl with xs ≟ ys
  -- ... | no ¬p    = no λ{ refl → ¬p refl }
  -- ... | yes refl = yes refl

  DecEq-Vec : {{_ : DecEq A}} → ∀ {n} → DecEq (Vec A n)
  DecEq-Vec ._≟_ = VecP.≡-dec _≟_

  DecEq-Maybe : {{_ : DecEq A}} → DecEq (Maybe A)
  DecEq-Maybe ._≟_ = MaybeP.≡-dec _≟_

  -- ** reflection
  DecEq-Name : DecEq Name
  DecEq-Name ._≟_ = _≟ₙ_

  DecEq-Term : DecEq Term
  DecEq-Term ._≟_ = _≟ₜ_

  DecEq-Arg : {{_ : DecEq A}} → DecEq (Arg A)
  DecEq-Arg ._≟_ = RArg.≡-dec _≟_

pattern `yes x  = quote _because_ ◆⟦ quote true ◆  ∣ quote ofʸ ◆⟦ x ⟧ ⟧
pattern ``yes x = quote _because_ ◇⟦ quote true ◇  ∣ quote ofʸ ◇⟦ x ⟧ ⟧
pattern `no x   = quote _because_ ◆⟦ quote false ◆ ∣ quote ofⁿ ◆⟦ x ⟧ ⟧
pattern ``no x  = quote _because_ ◇⟦ quote false ◇ ∣ quote ofⁿ ◇⟦ x ⟧ ⟧

compatible? : List Type → Type → Type → TC Bool
compatible? ctx ty ty′ = do
  print $ show ty <> " ≈? " <> show ty′
  b ← runSpeculative $ (_, false) <$>
    catchTC (unify (varsToUnknown ty) (varsToUnknown ty′) >> return true)
            (return false)
  print $ "  ——→ " <> show b
  return b

derive-DecEq : (Name × Name) → Definition → TC Term

derive-DecEq _              (data-type _ []) = return `λ∅
derive-DecEq (this , ≟-rec) (data-type pars cs) = do
  print $ "DATATYPE {pars = " <> show pars <> "; cs = " <> show cs <> "}"
  cls ← concatMap fromMaybe <$> traverse f (allPairs cs)
  return $ pat-lam cls []
  where
    go : ℕ → List (ℕ × Type) → Term
    go _ []              = `yes (quote refl ◆)
    go n ((x , ty) ∷ xs) =
      quote case_of_
        ∙⟦ quote _≟_ ∙⟦ # (x + n) ∣ # x ⟧
         ∣ `λ⟦ ``no (Pattern.var "¬p") ⇒ `no (`λ⟦ (quote refl ◇) ⇒ (# 0 ⟦ quote refl ◆ ⟧) ⟧)
             ∣ ``yes (quote refl ◇)    ⇒ go n xs ⟧ ⟧

    f : Name × Name → TC (Maybe Clause)
    f (c , c′) = do
      (pc  , _ , pvs) ← mkPattern c
      (pc′ , n , _)   ← mkPattern c′
      ty  ← getType c
      ty′ ← getType c′
      b   ← compatible? (unArgs $ argTys ty) (resultTy ty) (resultTy ty′)
      return $
        if b then
          just (if c == c′ then ⟦ pc ∣ mapVariables (_<> "′") pc ⇒ go n pvs ⟧
                           else ⟦ pc ∣ pc′ ⇒ `no `λ∅ ⟧)
        else nothing
derive-DecEq _ (record-type rn fs) = do
  print $ "RECORD {name = " <> show rn <> "; fs = " <> show fs <> "}"
  return $ `λ⟦ "r" ∣ "r′" ⇒ go fs ⟧
  where
    go : List (Arg Name) → Term
    go [] = `yes (quote refl ◆)
    go (arg (arg-info _ irrelevant) _ ∷ args) = go args
    go (arg (arg-info _ relevant)   n ∷ args) =
      quote case_of_
        ∙⟦ quote _≟_ ∙⟦ n ∙⟦ # 1 ⟧ ∣ n ∙⟦ # 0 ⟧ ⟧
         ∣ `λ⟦ ``no (Pattern.var "¬p")
             ⇒ `no (`λ⟦ (quote refl ◇) ⇒ (# 0 ⟦ quote refl ◆ ⟧) ⟧)
             ∣ ``yes (quote refl ◇)
             ⇒ go args
             ⟧
         ⟧
derive-DecEq _ _ = error "impossible"

instance
  Derivable-DecEq : Derivable DecEq
  Derivable-DecEq .DERIVE' xs = do
    print "*************************************************************************"
    (record-type c _) ← getDefinition (quote DecEq)
      where _ → error "impossible"

    -- ** Declare ⋯ fᵢ′ : Decidable {A = Tᵢ} _≡_ ⋯
    -- and define ⋯ instance
    --                fᵢ : DecEq Tᵢ ⋯
    --                fᵢ = ⋯
    --            ⋯
    ys ← forM xs λ{ (n , f) → do
      print $ "Deriving " <> parens (show f <> " : DecEq " <> show n)
      f′ ← freshName (show {A = Name} f)
      T ← getType n
      ctx ← getContext
      print $ "  Context: " <> show ctx
      print $ "  n: " <> show n
      print $ "  Type: " <> show T
      d ← getDefinition n
      let is = drop ({-parameters d-} length ctx) (argTys T)
      let n′ = apply⋯ is n
      print $ "  Parameters: " <> show (parameters d)
      print $ "  Indices: " <> show is
      print $ "  n′: " <> show n′
      t ← derive-DecEq (n , f′) d
      -- print $ "  Term: " <> show t
      let ty′ = ∀indices⋯ is $ def (quote Decidable) (hArg? ∷ hArg n′ ∷ hArg? ∷ hArg? ∷ vArg (quote _≡_ ∙) ∷ [])
      print $ "  Ty′: " <> show ty′
      declareDef (vArg f′) ty′
      let ty = ∀indices⋯ is $ quote DecEq ∙⟦ n′ ⟧
      print $ "  Ty: " <> show ty
      declareDef (iArg f) ty
      defineFun f (⟦⇒ c ◆⟦ f′ ∙ ⟧ ⟧ ∷ [])
      return (f′ , t)
      }

    -- ** Define ⋯ fᵢ′ : Decidable {A = Tᵢ} _≡_ ⋯
    return⊤ $ forM ys λ{ (f′ , t) → defineFun f′ (⟦⇒ t ⟧ ∷ []) }


private

-- ** list recursion

  data Nat : Set where
    O : Nat
    S : List Nat → Nat

  -- {-# TERMINATING #-}
{- *** T0D0: figure out how to pass termination checker
-}

  go : Decidable {A = Nat} _≡_
  instance
    dn : DecEq Nat
    dn ._≟_ = go

  -- gos : Decidable {A = List Nat} _≡_
  -- gos = ListP.≡-dec go
  -- gos [] []      = yes refl
  -- gos [] (_ ∷ _) = no λ()
  -- gos (_ ∷ _) [] = no λ()
  -- gos (x ∷ xs) (y ∷ ys) with x ≟ y
  -- ... | no ¬p    = no λ{ refl → ¬p refl }
  -- ... | yes refl with gos xs ys
  -- ... | no ¬p    = no λ{ refl → ¬p refl }
  -- ... | yes refl = yes refl

  go = λ
    { O O → yes refl
    ; O (S x0) → no (λ { () })
    ; (S x0) O → no (λ { () })
    ; (S x0) (S x0′)
        → case x0 ≟ x0′ of λ
            { (no ¬p) → no λ { refl → ¬p refl }
            ; (yes refl) → yes refl }}
  -- unquoteDecl DecEq-Nats = DERIVE DecEq [ quote Nats , DecEq-Nats ]
