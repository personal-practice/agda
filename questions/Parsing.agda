module Parsing where

open import Level
open import Function
open import Category.Monad

open import Data.Product
open import Data.Char
open import Data.String as Str
open import Data.Bool
open import Data.Nat
open import Data.Maybe
open import Data.List using (List; []; _∷_)
import Data.List.NonEmpty as List⁺

open import Relation.Unary

open import Text.Parser 0ℓ
open import Induction.Nat.Strong as Box using (□_)

data 𝟙 : Set where
  one : 𝟙

p𝟙 : ∀[ Parser [ 𝟙 ] ]
p𝟙 = one <$ char '1'

p𝟚 : ∀[ Parser [ Bool ] ]
p𝟚 = true  <$ text "true"
 <|> false <$ text "false"

pchar : ∀[ Parser [ Char ] ]
pchar = alpha

anyChar : ∀[ Parser [ Char ] ]
anyChar = anyTok

anyString : ∀[ Parser [ String ] ]
anyString = Str.fromList ∘ List⁺.toList <$> list⁺ anyChar

private variable A B : Set

pmaybe : ∀[ Parser [ A ] ⇒ Parser [ B ] ⇒ Parser [ Maybe A × B ] ]
pmaybe pa pb = ((nothing ,_) <$> pb)
     <|> ((just <$> pa) <&> box pb)

list : ∀[ Parser [ A ] ⇒ Parser [ List A ] ]
list {A = A} = Box.fix (Parser [ A ] ⇒ Parser [ List A ]) $ λ rec pA →
          uncurry (λ hd → (hd ∷_) ∘′ maybe id [])
          <$> (pA <&?> (Box.app rec (box pA)))
