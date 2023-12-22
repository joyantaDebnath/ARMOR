open import Armor.Binary
open import Armor.Data.X509.Cert.Properties
open import Armor.Data.X509.Cert.TCB
open import Armor.Data.X509.Extension.TCB
open import Armor.Data.X509.Name.TCB
open import Armor.Data.X509.SignAlg
open import Armor.Data.X509.TBSCert
import      Armor.Data.X509.TBSCert.UID.TCB as TBSCert
open import Armor.Data.X690-DER.BitString
open import Armor.Data.X690-DER.Int.TCB
open import Armor.Data.X690-DER.TLV
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Definitions
import      Armor.Grammar.IList
import      Armor.Grammar.Option
import      Armor.Grammar.Parallel
import      Armor.Grammar.Seq
open import Armor.Prelude

module Armor.Data.X509.Cert.Eq where

open Armor.Grammar.Definitions  UInt8
open Armor.Grammar.IList        UInt8
open Armor.Grammar.Parallel     UInt8
open Armor.Grammar.Option       UInt8
open Armor.Grammar.Seq          UInt8

instance
  eq≋ : Eq≋ CertFields
  eq≋ = Iso.isoEq≋ iso
          (Seq.eq≋&ₚ (Parallel.eq≋Σₚ it λ _ → it)
            (Seq.eq≋&ₚ it (Parallel.eq≋Σₚ it λ _ → it)))

  eq : Eq (Exists─ _ CertFields)
  eq = Eq≋⇒Eq it
