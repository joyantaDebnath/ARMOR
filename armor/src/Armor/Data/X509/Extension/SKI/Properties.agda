open import Armor.Binary
open import Armor.Data.X509.Extension.SKI.TCB
open import Armor.Data.X690-DER.OctetString
open import Armor.Data.X690-DER.TLV
import      Armor.Grammar.Definitions
import      Armor.Grammar.Properties

open import Armor.Prelude

module Armor.Data.X509.Extension.SKI.Properties where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Properties  UInt8

@0 unambiguous : Unambiguous SKIFields
unambiguous = TLV.unambiguous OctetString.unambiguous

@0 nonmalleable : NonMalleable RawSKIFields
nonmalleable = TLV.nonmalleable OctetString.nonmalleable
