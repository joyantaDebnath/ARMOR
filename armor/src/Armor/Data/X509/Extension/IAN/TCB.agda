open import Armor.Binary
open import Armor.Data.X509.GeneralNames.TCB
open import Armor.Data.X690-DER.TLV.TCB
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Definitions.NonMalleable
open import Armor.Prelude

module Armor.Data.X509.Extension.IAN.TCB where

open Armor.Grammar.Definitions.NonMalleable UInt8

-- https://datatracker.ietf.org/doc/html/rfc5280#section-4.2.1.7
--    id-ce-issuerAltName OBJECT IDENTIFIER ::=  { id-ce 18 }

--    IssuerAltName ::= GeneralNames
   
IANFields : @0 List UInt8 → Set
IANFields xs = TLV Tag.OctetString GeneralNames xs

RawIANFields : Raw IANFields
RawIANFields = RawTLV _ RawGeneralNames
