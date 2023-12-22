open import Armor.Binary
open import Armor.Data.X509.Extension
import      Armor.Data.X509.Extension.TCB.OIDs as OIDs
open import Armor.Data.X509.PublicKey
open import Armor.Data.X509.Name
open import Armor.Data.X509.SignAlg
open import Armor.Data.X509.TBSCert.Properties
open import Armor.Data.X509.TBSCert.TCB
open import Armor.Data.X509.TBSCert.UID.TCB
open import Armor.Data.X509.TBSCert.Version
open import Armor.Data.X509.Validity
open import Armor.Data.X690-DER.BitString
open import Armor.Data.X690-DER.Default
open import Armor.Data.X690-DER.Int
import      Armor.Data.X690-DER.OctetString.Properties
open import Armor.Data.X690-DER.SetOf
open import Armor.Data.X690-DER.SequenceOf
open import Armor.Data.X690-DER.TLV
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Definitions
import      Armor.Grammar.Option
import      Armor.Grammar.Parallel
import      Armor.Grammar.Properties
import      Armor.Grammar.Seq
open import Armor.Prelude

module Armor.Data.X509.TBSCert.Eq where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Option      UInt8
open Armor.Grammar.Parallel    UInt8
open Armor.Grammar.Properties  UInt8
open Armor.Grammar.Seq         UInt8

instance
  eq≋ : Eq≋ TBSCertFields
  eq≋ =
    Iso.isoEq≋ iso
      (Seq.eq≋&ₚ (Seq.eq≋&ₚ it it)
      (Seq.eq≋&ₚ it
      (Seq.eq≋&ₚ it
      (Seq.eq≋&ₚ it
      (Seq.eq≋&ₚ it
      (Seq.eq≋&ₚ (Parallel.eq≋Σₚ it λ _ → record { _≟_ = λ where self self → yes refl })
      (Seq.eq≋&ₚ it
      (Seq.eq≋&ₚ it it))))))))
    where
    instance
      e₁ : Eq≋ (NonEmptySequenceOf Extension)
      e₁ = SequenceOf.BoundedSequenceOfEq≋

      e₂ : Eq≋ (Default [0]ExplicitVersion v1[0]ExplicitVersion)
      e₂ = Default.eq≋ v1[0]ExplicitVersion

  eq : Eq (Exists─ _ TBSCertFields)
  eq = Eq≋⇒Eq it
