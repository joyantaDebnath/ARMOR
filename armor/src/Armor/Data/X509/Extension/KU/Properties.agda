open import Armor.Binary
open import Armor.Data.X509.Extension.KU.TCB
open import Armor.Data.X690-DER.TLV
import      Armor.Grammar.Definitions
import      Armor.Grammar.Properties
open import Armor.Data.X690-DER.BitString
open import Armor.Data.X690-DER.SequenceOf

open import Armor.Prelude

module Armor.Data.X509.Extension.KU.Properties where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Properties  UInt8

@0 unambiguous : Unambiguous KUFields
unambiguous = TLV.unambiguous BitString.unambiguous

@0 nonmalleable : NonMalleable RawKUFields
nonmalleable = TLV.nonmalleable BitString.nonmalleable
