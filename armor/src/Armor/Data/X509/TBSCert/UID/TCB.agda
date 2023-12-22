open import Armor.Binary
open import Armor.Data.X690-DER.BitString.TCB
open import Armor.Data.X690-DER.TLV.TCB
import      Armor.Data.X690-DER.Tag as Tag
open import Armor.Prelude

module Armor.Data.X509.TBSCert.UID.TCB where

-- https://datatracker.ietf.org/doc/html/rfc5280#section-4.1
-- UniqueIdentifier  ::=  BIT STRING

IssUID : (@0 _ : List UInt8) → Set
IssUID xs = TLV Tag.A81 BitStringValue xs

SubUID : (@0 _ : List UInt8) → Set
SubUID xs = TLV Tag.A82 BitStringValue xs
