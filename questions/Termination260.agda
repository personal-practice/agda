-- see https://github.com/agda/agda/issues/5065
open import Data.Nat
open import Data.List
open import Data.Product
open import Data.Maybe
open import Data.Bool

HashId = ℕ
postulate _♯ : ∀ {A : Set ℓ} → A → HashId
Value = List (ℕ × ℕ)

postulate DATA : Set

record IsData (A : Set) : Set where
  field
    toData : A → DATA
    fromData : DATA → Maybe A
open IsData ⦃...⦄

postulate TxInfo : Set
record Pending : Set where
  field
    txInfo : TxInfo
    this   : HashId
open Pending public
Validator = Pending → Bool
MonetaryPolicy = Pending → Bool

postulate thisValidator : Pending → HashId
-- thisValidator record {this = i; txInfo = record {inputInfo = is}} = InputInfo.validatorHash (is ‼ i)

postulate propagates : Value → Pending → Bool
-- propagates v ptx@(record {txInfo = txi})
--   = (valueAtⁱ ℍ txi ≥ᶜ v)
--   ∧ (valueAtᵒ ℍ txi ≥ᶜ v)
--   where ℍ = thisValidator ptx

postulate
  lookupQuantity : ℕ → Value → ℕ
  randomAddress : TxInfo → HashId
  getForge : TxInfo → Value

mutual
  policy : MonetaryPolicy
  policy pti@(record {this = c; txInfo = txi}) =
      ⌊ lookupQuantity c (getForge txi) ≟ 1 ⌋
    ∧ ⌊ randomAddress txi ≟ 𝕍 ⌋

  ℂ : HashId
  ℂ = policy ♯

  thread : Value
  thread = [ ℂ , 1 ]

  validator : Validator
  validator = propagates thread

  𝕍 : HashId
  𝕍 = validator ♯
