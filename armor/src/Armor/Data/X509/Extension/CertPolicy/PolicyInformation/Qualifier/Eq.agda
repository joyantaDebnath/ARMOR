open import Armor.Binary
open import Armor.Data.X509.Extension.CertPolicy.PolicyInformation.Qualifier.Properties
open import Armor.Data.X509.Extension.CertPolicy.PolicyInformation.Qualifier.TCB
import      Armor.Data.X509.Extension.CertPolicy.PolicyInformation.Qualifier.TCB.OIDs as OIDs
open import Armor.Data.X509.Extension.CertPolicy.PolicyInformation.Qualifier.UserNotice
open import Armor.Data.X690-DER.OID
open import Armor.Data.X690-DER.Sequence.DefinedByOID
open import Armor.Data.X690-DER.SequenceOf.TCB
open import Armor.Data.X690-DER.Strings
open import Armor.Data.X690-DER.TLV
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Definitions
import      Armor.Grammar.Parallel
import      Armor.Grammar.Sum
open import Armor.Prelude

module Armor.Data.X509.Extension.CertPolicy.PolicyInformation.Qualifier.Eq where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Parallel    UInt8
open Armor.Grammar.Sum         UInt8

instance
  eq≋CPS : Eq≋ CPSURIQualifier
  eq≋CPS =
    DefinedByOID.eq≋ _ λ _ →
      Parallel.eq≋Σₚ it λ _ →
        record
          { _≟_ = λ where
            ≋-refl ≋-refl → yes refl
          }

  eq≋UserNotice : Eq≋ UserNoticeQualifier
  eq≋UserNotice =
    DefinedByOID.eq≋ _ λ _ →
      Parallel.eq≋Σₚ it λ _ →
        record
          { _≟_ = λ where
            ≋-refl ≋-refl → yes refl
          }

  eq≋ : Eq≋ PolicyQualifierInfoFields
  eq≋ = Iso.isoEq≋ iso Sum.sumEq≋
