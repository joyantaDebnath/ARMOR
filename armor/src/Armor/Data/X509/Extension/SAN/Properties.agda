open import Armor.Binary
open import Armor.Data.X509.Extension.SAN.TCB
open import Armor.Data.X690-DER.OctetString
open import Armor.Data.X690-DER.TLV
import      Armor.Grammar.Definitions
import      Armor.Grammar.Properties
open import       Armor.Data.X509.GeneralNames

open import Armor.Prelude

module Armor.Data.X509.Extension.SAN.Properties where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Properties  UInt8

@0 unambiguous : Unambiguous SANFields
unambiguous = TLV.unambiguous GeneralNames.unambiguous

@0 nonmalleable : NonMalleable RawSANFields
nonmalleable = TLV.nonmalleable GeneralNames.nonmalleable
