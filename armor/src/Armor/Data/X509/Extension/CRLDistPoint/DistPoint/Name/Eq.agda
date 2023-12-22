open import Armor.Binary
open import Armor.Data.X509.Extension.CRLDistPoint.DistPoint.Name.Properties
open import Armor.Data.X509.Extension.CRLDistPoint.DistPoint.Name.TCB
open import Armor.Data.X509.GeneralNames
open import Armor.Data.X509.Name
open import Armor.Data.X690-DER.SetOf
open import Armor.Data.X690-DER.SequenceOf
open import Armor.Data.X690-DER.TLV
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Definitions
import      Armor.Grammar.Sum
open import Armor.Prelude

module Armor.Data.X509.Extension.CRLDistPoint.DistPoint.Name.Eq where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Sum         UInt8

instance
  eq≋ : Eq≋ DistPointNameChoice
  eq≋ = Iso.isoEq≋ iso Sum.sumEq≋
