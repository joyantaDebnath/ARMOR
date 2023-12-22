open import Armor.Binary
open import Armor.Data.X509.GeneralNames.TCB
open import Armor.Data.X509.GeneralNames.GeneralName.Eq
open import Armor.Data.X509.Name
open import Armor.Data.X690-DER
open import Armor.Data.X690-DER.TLV
import      Armor.Grammar.Definitions
import      Armor.Grammar.Sum
open import Armor.Prelude
open import Data.Nat.Properties
  hiding (_≟_)

module Armor.Data.X509.GeneralNames.Eq where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Sum         UInt8

instance
  eq≋Elems : Eq≋ GeneralNamesElems
  eq≋Elems = SequenceOf.BoundedSequenceOfEq≋
