open import Armor.Binary
open import Armor.Data.X690-DER.Length
open import Armor.Data.X690-DER.TLV.TCB
open import Armor.Prelude

module Armor.Data.X690-DER.TLV.Serializer
  {A : @0 List UInt8 → Set} (ser : ∀ {@0 bs} → A bs → Singleton bs)
  where

serialize : ∀ {@0 bs} {t} → TLV t A bs → Singleton bs
serialize{t = t} (mkTLV len val len≡ bs≡)
  with Length.serialize len
  |    ser val
... | singleton l refl | singleton v refl =
  singleton (t ∷ l ++ v) (sym bs≡)
