open import Armor.Binary
open import Armor.Prelude

module Armor.Data.X690-DER.Length where

module Length where
  open import Armor.Data.X690-DER.Length.TCB        public
  open import Armor.Data.X690-DER.Length.Properties public
  open import Armor.Data.X690-DER.Length.Serializer public

open Length public
  using (Length ; getLength)
  hiding (module Length)

open import Armor.Data.X690-DER.Length.Parser public
