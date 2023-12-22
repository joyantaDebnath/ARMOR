open import Armor.Binary
open import Armor.Data.X509.Extension.NC.GeneralSubtree.Properties
open import Armor.Data.X509.Extension.NC.GeneralSubtree.TCB
open import Armor.Data.X509.GeneralNames
open import Armor.Data.X690-DER.Default
open import Armor.Data.X690-DER.Int
import      Armor.Data.X690-DER.OctetString.Properties as OctetString
open import Armor.Data.X690-DER.TLV
import      Armor.Data.X690-DER.Tag as Tag
open import Armor.Data.X690-DER.SequenceOf.TCB
import      Armor.Grammar.Definitions
import      Armor.Grammar.Option
import      Armor.Grammar.Properties
import      Armor.Grammar.Seq
open import Armor.Prelude

module Armor.Data.X509.Extension.NC.GeneralSubtree.Eq where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Option      UInt8
open Armor.Grammar.Properties  UInt8
open Armor.Grammar.Seq         UInt8

instance
  eq≋ : Eq≋ GeneralSubtreeFields
  eq≋ = Iso.isoEq≋ iso (Seq.eq≋&ₚ it (Seq.eq≋&ₚ (Default.eq≋ _) it))
