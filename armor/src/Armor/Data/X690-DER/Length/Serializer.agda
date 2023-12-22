open import Armor.Binary
open import Armor.Data.X690-DER.Length.TCB
open import Armor.Prelude

module Armor.Data.X690-DER.Length.Serializer where

serialize : ∀ {@0 bs} → Length bs → Singleton bs
serialize (short (mkShort l l<128 bs≡)) =
  singleton _ (sym bs≡)
serialize (long (mkLong l l>128 lₕ lₕ≢0 lₜ lₜLen lₕₜMinRepLong bs≡)) =
  singleton _ (sym bs≡)
