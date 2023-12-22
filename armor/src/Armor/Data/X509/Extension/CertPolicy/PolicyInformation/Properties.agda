open import Armor.Binary
open import Armor.Data.X509.Extension.CertPolicy.PolicyInformation.Qualifier
open import Armor.Data.X509.Extension.CertPolicy.PolicyInformation.TCB
open import Armor.Data.X690-DER.OID
open import Armor.Data.X690-DER.TLV
open import Armor.Data.X690-DER.SequenceOf
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Definitions
import      Armor.Grammar.Option
import      Armor.Grammar.Properties
import      Armor.Grammar.Seq
open import Armor.Prelude

module Armor.Data.X509.Extension.CertPolicy.PolicyInformation.Properties where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Option      UInt8
open Armor.Grammar.Properties  UInt8
open Armor.Grammar.Seq         UInt8

iso : Iso PolicyInformationFieldsRep PolicyInformationFields
proj₁ (proj₁ iso) (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = mkPolicyInformationFields fstₚ₁ sndₚ₁ bs≡
proj₂ (proj₁ iso) (mkPolicyInformationFields cpid cpqls bs≡) = mk&ₚ cpid cpqls bs≡
proj₁ (proj₂ iso) (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = refl
proj₂ (proj₂ iso) (mkPolicyInformationFields cpid cpqls bs≡) = refl

@0 unambiguous : Unambiguous PolicyInformation
unambiguous = TLV.unambiguous
  (Iso.unambiguous iso
    (Unambiguous.unambiguous-&₁option₁
      OID.unambiguous TLV.nosubstrings
      Qualifier.unambiguous
      TLV.nonempty))

@0 nonmalleable : NonMalleable RawPolicyInformation
nonmalleable = TLV.nonmalleable
  (Iso.nonmalleable iso
    RawPolicyInformationFieldsRep
      (Seq.nonmalleable OID.nonmalleable
        (Option.nonmalleable _ Qualifier.nonmalleable)))
