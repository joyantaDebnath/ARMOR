open import Armor.Binary
open import Armor.Data.X509.GeneralNames
open import Armor.Data.X509.Extension.CRLDistPoint.DistPoint.Name
open import Armor.Data.X509.Extension.CRLDistPoint.DistPoint.Properties
open import Armor.Data.X509.Extension.CRLDistPoint.DistPoint.TCB
open import Armor.Data.X690-DER.BitString
open import Armor.Data.X690-DER.TLV
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Definitions
import      Armor.Grammar.Option
import      Armor.Grammar.Seq
open import Armor.Prelude

module Armor.Data.X509.Extension.CRLDistPoint.DistPoint.Eq where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Option      UInt8
open Armor.Grammar.Seq         UInt8

instance
  eq≋ : Eq≋ DistPointFields
  eq≋ = Iso.isoEq≋ iso (Seq.eq≋&ₚ it (Seq.eq≋&ₚ it it))
