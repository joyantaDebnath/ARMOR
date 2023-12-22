open import Armor.Binary
open import Armor.Data.X509.GeneralNames.TCB
open import Armor.Data.X509.GeneralNames.GeneralName
open import Armor.Data.X509.Name
open import Armor.Data.X690-DER
import      Armor.Grammar.Definitions
import      Armor.Grammar.Properties
import      Armor.Grammar.Sum
open import Armor.Prelude
open import Data.Nat.Properties
  hiding (_≟_)

module Armor.Data.X509.GeneralNames.Properties where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Properties  UInt8
open Armor.Grammar.Sum         UInt8

module GeneralNamesElems where
  @0 unambiguous : Unambiguous GeneralNamesElems
  unambiguous =
    SequenceOf.Bounded.unambiguous
      GeneralName.unambiguous GeneralName.nonempty GeneralName.nosubstrings

  @0 nonmalleable : NonMalleable RawGeneralNamesElems
  nonmalleable = SequenceOf.Bounded.nonmalleable{R = RawGeneralName} GeneralName.nonempty GeneralName.nosubstrings GeneralName.nonmalleable

@0 unambiguous : Unambiguous GeneralNames
unambiguous = TLV.unambiguous GeneralNamesElems.unambiguous

@0 nonmalleable : NonMalleable RawGeneralNames
nonmalleable = TLV.nonmalleable{R = RawGeneralNamesElems} GeneralNamesElems.nonmalleable
