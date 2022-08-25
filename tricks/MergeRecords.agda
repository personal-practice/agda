module MergeRecords where

open import Prelude.Init

record R₁ : Set where
  field x : ℕ

record R₂ : Set where
  field y : ℕ

Record = List (String × Type)

Field = Arg Name
Fields = Args Name

mkRecord : Name → Fields → TC Record
mkRecord c fs = ?

macro
  reify : Name → Tactic
  reify n hole = do
    record-type c fs ← getDefinition n
      where _ → error "[reify] not a record"
    t ← mkRecord c fs
    unify hole t

private
  _ = reify R₁ ≡ [ "x" , quoteTerm ℕ ] ∋ refl
  _ = reify R₂ ≡ [ "y" , quoteTerm ℕ ] ∋ refl

reflect : Name → Record → TC ⊤
reflect f r = do
  defineRec ...

unquoteDecl R₃ = reflect R₃ (reify R₁)


_≔_∗_ : Name → Name → Name → TC ⊤
f ≔ n ∗ n′ = do
  record-type r fs ← getDefinition n
    where _ → error "[reflect] not a record"
  record-type r′ fs′ ← getDefinition n′
    where _ → error "[reflect] not a record"


-- record R³ : Set where
--   field x : ℕ
--         y : ℕ
unquoteDecl R³′ = R³ ≔ quote R₁ ∗ quote R₂
