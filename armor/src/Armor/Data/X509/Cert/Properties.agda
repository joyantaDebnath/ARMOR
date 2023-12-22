open import Armor.Binary
open import Armor.Data.X509.Cert.TCB
open import Armor.Data.X509.Extension.TCB
open import Armor.Data.X509.Name.TCB
open import Armor.Data.X509.SignAlg
open import Armor.Data.X509.TBSCert
import      Armor.Data.X509.TBSCert.UID.TCB as TBSCert
open import Armor.Data.X690-DER.BitString
open import Armor.Data.X690-DER.OctetString
open import Armor.Data.X690-DER.SequenceOf
open import Armor.Data.X690-DER.TLV
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Definitions
import      Armor.Grammar.IList
import      Armor.Grammar.Option
import      Armor.Grammar.Parallel
import      Armor.Grammar.Seq
open import Armor.Prelude

module Armor.Data.X509.Cert.Properties where

open Armor.Grammar.Definitions  UInt8
open Armor.Grammar.IList        UInt8
open Armor.Grammar.Option       UInt8
open Armor.Grammar.Parallel     UInt8
open Armor.Grammar.Seq          UInt8

-- instance
--   CertEq : Eq (Exists─ (List UInt8) CertFields)
--   CertEq = (isoEq iso eq)
--     where
--     eq : Eq (Exists─ (List UInt8) Rep)
--     eq = eq&ₚ (eqΣₚ it λ _ → it)
--            (eq&ₚ it
--              (eqΣₚ (Eq≋⇒Eq (TLV.EqTLV ⦃ Eq⇒Eq≋ BitString.eq ⦄)) λ _ → it))

iso   : Iso CertFieldsRep CertFields
proj₁ iso = equivalentCertFields
proj₁ (proj₂ iso) (mk&ₚ (mk×ₚ fstₚ₁ s) (mk&ₚ fstₚ₂ (mk×ₚ sndₚ₁ _) refl) refl) = refl
proj₂ (proj₂ iso) (mkCertFields tbs tbsBytes signAlg signature sbytes refl) = refl

RawRep₁ = Raw&ₚ RawSignAlg (Raw×ₚ RawBitString RawOctetStringValue)
RawRep = Raw&ₚ (Raw×ₚ RawTBSCert RawOctetStringValue) RawRep₁

@0 unambiguous : Unambiguous Cert
unambiguous =
  TLV.unambiguous (Iso.unambiguous iso
    (Seq.unambiguous
      (Parallel.unambiguous (TBSCert.unambiguous) (λ where _ self self → refl))
      (Parallel.nosubstrings₁ TLV.nosubstrings)
      (Seq.unambiguous SignAlg.unambiguous SignAlg.nosubstrings
        (Parallel.unambiguous BitString.unambiguous (λ where _ self self → refl)))))

@0 nonmalleableFields : NonMalleable RawCertFields
nonmalleableFields =
  Iso.nonmalleable iso RawCertFieldsRep
    nm₁
  where
  nm₂ : NonMalleable (Raw&ₚ RawSignAlg (Raw×ₚ RawBitString RawOctetStringValue))
  nm₂ =
    Seq.nonmalleable
      {ra = RawSignAlg}
      {rb = Raw×ₚ RawBitString RawOctetStringValue}
      SignAlg.nonmalleable
      (Parallel.nonmalleable×ₚ{ra = RawBitString}{rb = RawOctetStringValue}
        BitString.nonmalleable
        OctetString.nonmalleableValue)

  nm₁ : NonMalleable RawCertFieldsRep
  nm₁ =
    Seq.nonmalleable
      {ra = Raw×ₚ RawTBSCert RawOctetStringValue}
      {rb = Raw&ₚ RawSignAlg (Raw×ₚ RawBitString RawOctetStringValue)}
      (Parallel.nonmalleable×ₚ TBSCert.nonmalleable λ where self self refl → refl)
      nm₂

@0 nonmalleable : NonMalleable RawCert
nonmalleable = TLV.nonmalleable{R = RawCertFields} nonmalleableFields

@0 nonmalleableCertList : NonMalleable RawCertList
nonmalleableCertList = SequenceOf.nonmalleable{R = RawCert} TLV.nonempty TLV.nosubstrings nonmalleable
