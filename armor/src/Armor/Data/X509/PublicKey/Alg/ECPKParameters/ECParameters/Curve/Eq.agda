open import Armor.Binary
open import Armor.Data.X509.PublicKey.Alg.ECPKParameters.ECParameters.Curve.TCB
open import Armor.Data.X509.PublicKey.Alg.ECPKParameters.ECParameters.Curve.Properties
open import Armor.Data.X690-DER.BitString
open import Armor.Data.X690-DER.OctetString
open import Armor.Data.X690-DER.TLV
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Definitions
import      Armor.Grammar.Option
import      Armor.Grammar.Properties
import      Armor.Grammar.Seq       
open import Armor.Prelude

module Armor.Data.X509.PublicKey.Alg.ECPKParameters.ECParameters.Curve.Eq where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Option      UInt8
open Armor.Grammar.Properties  UInt8
open Armor.Grammar.Seq         UInt8

instance
  eq≋ : Eq≋ CurveFields
  eq≋ =
    Iso.isoEq≋ iso
      (Eq⇒Eq≋ (Seq.eq&ₚ (Seq.eq&ₚ it it) it))

  eq : Eq (Exists─ _ CurveFields)
  eq = Eq≋⇒Eq it
