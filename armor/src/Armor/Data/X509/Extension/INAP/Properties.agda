open import Armor.Binary
open import Armor.Data.X509.Extension.INAP.TCB
open import Armor.Data.X690-DER.TLV
import      Armor.Grammar.Definitions
import      Armor.Grammar.Properties
open import Armor.Data.X690-DER.Int

open import Armor.Prelude

module Armor.Data.X509.Extension.INAP.Properties where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Properties  UInt8

@0 unambiguous : Unambiguous INAPFields
unambiguous = TLV.unambiguous Int.unambiguous

@0 nonmalleable : NonMalleable RawINAPFields
nonmalleable = TLV.nonmalleable Int.nonmalleable
