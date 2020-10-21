open import Agda.Builtin.Nat
open import Agda.Builtin.List
open import Agda.Builtin.String
open import Agda.Builtin.IO
open import Agda.Builtin.Unit

{-# FOREIGN GHC
import Data.Text
import qualified Data.Text.IO as Text

data Value = Number Integer | String Text
  deriving (Show)

class ToJSON a where
  toJSON :: a -> Value

data WithToJSON a = WithToJSON (a -> Value) a

instance ToJSON (WithToJSON a) where
  toJSON (WithToJSON f x) = f x

instance ToJSON Value where
  toJSON = id

encode :: ToJSON a => a -> Text
encode = pack . show . toJSON

#-}

data Value : Set where
  number : Nat → Value
  string : String → Value

{-# COMPILE GHC Value = data Value (Number | String) #-}

variable
  A : Set

data WithToJSON (A : Set) : Set where
  mkWithToJSON : (A → Value) → A → WithToJSON A

{-# COMPILE GHC WithToJSON = data WithToJSON (WithToJSON) #-}

record ToJSON (A : Set) : Set where
  field
    toJSON : A → Value

open ToJSON ⦃ ... ⦄

withToJSON : ⦃ ToJSON A ⦄ → A → WithToJSON A
withToJSON x = mkWithToJSON toJSON x

postulate
  encodeDyn : WithToJSON A → String

{-# COMPILE GHC encodeDyn = \ _ -> encode #-}

encode : ⦃ ToJSON A ⦄ → A → String
encode x = encodeDyn (withToJSON x)

instance
  toJSONNat : ToJSON Nat
  toJSONNat .toJSON = number

postulate
  putStrLn : String → IO ⊤

{-# COMPILE GHC putStrLn = Text.putStrLn #-}

main : IO ⊤
main = putStrLn (encode 17)
