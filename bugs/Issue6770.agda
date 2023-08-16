{-
open import Agda.Builtin.Equality
postulate
  X Y : Set
  f : X → Y
  P : Y → Set
variable
  x : X
module M (x : X) where
  y = f x
-- ** these all work
module _ {x} (open M x) where
  postulate _ : P y
postulate
  _ : let open M x in P y
  _ : (open M x) → P y
-- ** this raises unexpected error on `y`, suggesting that it has not been properly instantiated
module _ (open M x) where
  postulate _ : P y
-}

open import Prelude.Init hiding (module M); open SetAsType

open import SecureCompilation.ModuleParameters using (⋯)
module _ (⋯ : ⋯) where
  open import BitML (⋯ .⋯.⋯′) hiding (G; _↝_; module ∣AD)

  module M (ad : Ad) where
    G = ad .Ad.G

  postulate P : Precondition → Type

  -- ** IMPOSSIBLE
  module _ (open M ad) where
    postulate _ : P G
{-
An internal error has occurred. Please report this as a bug.
Location of the error: __IMPOSSIBLE__, called at src/full/Agda/TypeChecking/Substitute.hs:141:33
-}
