module TerminationRecords where

open import Data.Unit
open import Data.Bool
open import Data.List

record X : Set where
  field
    bs : List Bool

rec : X → ⊤
rec x@(record {bs = []}) = tt
rec x@(record {bs = b ∷ bs})
  with b
... | true = tt
... | false = rec (record x {bs = bs})


-- This works, but some more complicated use of this pattern has blocked me in UTxO.TxUtilities (lookupDatum≡)
