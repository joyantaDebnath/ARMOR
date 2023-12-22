open import Armor.Binary
open import Armor.Data.X509.Extension.TCB
open import Armor.Data.X509.PublicKey.TCB
import      Armor.Data.X509.Name.TCB as Name
open import Armor.Data.X509.SignAlg.TCB
open import Armor.Data.X509.TBSCert.UID.TCB
import      Armor.Data.X509.TBSCert.Version.Eq
import      Armor.Data.X509.TBSCert.Version.TCB as Version
import      Armor.Data.X509.Validity.TCB as Validity
open import Armor.Data.X509.Validity.Time.TCB
open import Armor.Data.X690-DER.Default.TCB
import      Armor.Data.X690-DER.Int.TCB as Int
open import Armor.Data.X690-DER.BitString.TCB as BitString
open import Armor.Data.X690-DER.OctetString.TCB as OctetString
import      Armor.Data.X690-DER.SequenceOf as SequenceOf
import      Armor.Data.X690-DER.TLV.Properties
open import Armor.Data.X690-DER.TLV.TCB
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Option
import      Armor.Grammar.Sum
import      Armor.Grammar.Seq
import      Armor.Grammar.Parallel
import      Armor.Grammar.Definitions
open import Armor.Prelude
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Armor.Data.X509.TBSCert.TCB where

open Armor.Grammar.Sum    UInt8
open Armor.Grammar.Seq    UInt8
open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Option      UInt8
open Armor.Grammar.Parallel    UInt8
open Int     hiding (getVal)
open Name     using  (Name)
open SequenceOf using (SequenceOf)
open Validity using (Validity)
open Version
  using (DecodedVersion ; [0]ExplicitVersion ; v1[0]ExplicitVersion ; Raw[0]ExplicitVersion)

{- https://datatracker.ietf.org/doc/html/rfc5280#section-4.1
-- The X.509 v3 certificate basic syntax is as follows.  For signature
-- calculation, the data that is to be signed is encoded using the ASN.1
-- distinguished encoding rules (DER) [X.690].  ASN.1 DER encoding is a
-- tag, length, value encoding system for each element.
--
-- TBSCertificate  ::=  SEQUENCE  {
--       version         [0]  EXPLICIT Version DEFAULT v1,
--       serialNumber         CertificateSerialNumber,
--       signature            AlgorithmIdentifier,
--       issuer               Name,
--       validity             Validity,
--       subject              Name,
--       subjectPublicKeyInfo SubjectPublicKeyInfo,
--       issuerUniqueID  [1]  IMPLICIT UniqueIdentifier OPTIONAL,
--                            -- If present, version MUST be v2 or v3
--       subjectUniqueID [2]  IMPLICIT UniqueIdentifier OPTIONAL,
--                            -- If present, version MUST be v2 or v3
--       extensions      [3]  EXPLICIT Extensions OPTIONAL
--                            -- If present, version MUST be v3
--       }
-- 
-}

-- https://datatracker.ietf.org/doc/html/rfc5280#section-4.1
--    CertificateSerialNumber  ::=  INTEGER

--    TBSCertificate  ::=  SEQUENCE  {
--         version         [0]  EXPLICIT Version DEFAULT v1,
--         serialNumber         CertificateSerialNumber,
--         signature            AlgorithmIdentifier,
--         issuer               Name,
--         validity             Validity,
--         subject              Name,
--         subjectPublicKeyInfo SubjectPublicKeyInfo,
--         issuerUniqueID  [1]  IMPLICIT UniqueIdentifier OPTIONAL,
--                              -- If present, version MUST be v2 or v3

--         subjectUniqueID [2]  IMPLICIT UniqueIdentifier OPTIONAL,
--                              -- If present, version MUST be v2 or v3
--         extensions      [3]  EXPLICIT Extensions OPTIONAL
--                              -- If present, version MUST be v3
--         }

record TBSCertFields (@0 bs : List UInt8) : Set where
  constructor mkTBSCertFields
  field
    @0 {ver ser sa i va u p u₁ u₂ e} : List UInt8
    version : Default [0]ExplicitVersion v1[0]ExplicitVersion ver
    serial  : Int ser
    signAlg : SignAlg sa
    issuer  : Name i
    validity : Validity va
    subject  : Name u
    pk       : PublicKey p
    pkBytes  : Singleton p -- TODO: eventually this should come from serialization
    issuerUID : Option IssUID u₁
    subjectUID : Option SubUID u₂
    extensions : Option Extensions e
    @0 bs≡  : bs ≡ ver ++ ser ++ sa ++ i ++ va ++ u ++ p ++ u₁ ++ u₂ ++ e

  getVersion : DecodedVersion
  getVersion = Raw.to (RawDefault Raw[0]ExplicitVersion _) version

  getSerial : ℤ
  getSerial = Int.getVal serial

  getValidityStartTime : Time _
  getValidityEndTime : Time _

  getValidityStartTime = Validity.getNBTime validity
  getValidityEndTime   = Validity.getNATime validity

  getIssuerLen : ℕ
  getIssuerLen = SequenceOf.lengthSequence (TLV.val issuer)

  getSubjectLen :  ℕ
  getSubjectLen = SequenceOf.lengthSequence (TLV.val subject)

  getSignAlg : Exists─ (List UInt8) SignAlg
  getSignAlg = _ , signAlg

  getBC : Exists─ (List UInt8) (Option ExtensionFieldBC)
  getBC = elimOption (_ , none) (λ v → Extensions.getBC v) extensions

  getKU : Exists─ (List UInt8) (Option ExtensionFieldKU)
  getKU = elimOption (_ , none) (λ v → Extensions.getKU v) extensions

  getEKU : Exists─ (List UInt8) (Option ExtensionFieldEKU)
  getEKU = elimOption (_ , none) (λ v → Extensions.getEKU v) extensions

  getSAN : Exists─ (List UInt8) (Option ExtensionFieldSAN)
  getSAN = elimOption (_ , none) (λ v → Extensions.getSAN v) extensions

  getCRLDIST : Exists─ (List UInt8) (Option ExtensionFieldCRLDist)
  getCRLDIST = elimOption (_ , none) (λ v → Extensions.getCRLDIST v) extensions

  getCPOL : Exists─ (List UInt8) (Option ExtensionFieldCPOL)
  getCPOL = elimOption (_ , none) (λ v → Extensions.getCPOL v) extensions

  getExtensionsList : List (Exists─ (List UInt8) Extension)
  getExtensionsList = elimOption [] (λ v → Extensions.getExtensionsList v) extensions

TBSCert : (@0 _ : List UInt8) → Set
TBSCert xs = TLV Tag.Sequence TBSCertFields xs

Rep₁ = &ₚ (Option SubUID) (Option Extensions)
Rep₂ = &ₚ (Option IssUID) Rep₁
Rep₃ = &ₚ (PublicKey ×ₚ Singleton) Rep₂
Rep₄ = &ₚ Name Rep₃
Rep₅ = &ₚ Validity Rep₄
Rep₆ = &ₚ Name Rep₅
Rep₇ = &ₚ SignAlg Rep₆

TBSCertFieldsRep : @0 List UInt8 → Set
TBSCertFieldsRep = (&ₚ (&ₚ (Default [0]ExplicitVersion v1[0]ExplicitVersion) Int) Rep₇)

equivalentTBSCertFields : Equivalent
               TBSCertFieldsRep
               TBSCertFields
proj₁ equivalentTBSCertFields (mk&ₚ (mk&ₚ fstₚ₁ sndₚ₁ refl) (mk&ₚ fstₚ₂ (mk&ₚ fstₚ₃ (mk&ₚ fstₚ₄ (mk&ₚ fstₚ₅ (mk&ₚ (mk×ₚ fstₚ₆ s) (mk&ₚ fstₚ₇ (mk&ₚ fstₚ₈ sndₚ₂ refl) refl) refl) refl) refl) refl) refl) bs≡) =
  mkTBSCertFields fstₚ₁ sndₚ₁ fstₚ₂ fstₚ₃ fstₚ₄ fstₚ₅ fstₚ₆ s fstₚ₇ fstₚ₈ sndₚ₂
    (trans₀ bs≡ (solve (++-monoid UInt8)))
proj₂ equivalentTBSCertFields (mkTBSCertFields version serial signAlg issuer validity subject pk pkBytes issuerUID subjectUID extensions bs≡) =
  mk&ₚ (mk&ₚ version serial refl) (mk&ₚ signAlg (mk&ₚ issuer (mk&ₚ validity (mk&ₚ subject (mk&ₚ (mk×ₚ pk pkBytes) (mk&ₚ issuerUID (mk&ₚ subjectUID extensions refl) refl) refl) refl) refl) refl) refl)
    (trans₀ bs≡ (solve (++-monoid UInt8)))

RawTBSCertFieldsRep : Raw TBSCertFieldsRep
RawTBSCertFieldsRep = Raw&ₚ (Raw&ₚ (RawDefault Raw[0]ExplicitVersion v1[0]ExplicitVersion) RawInt)
                      (Raw&ₚ RawSignAlg
                      (Raw&ₚ Name.RawName
                      (Raw&ₚ Validity.RawValidity
                      (Raw&ₚ Name.RawName
                      (Raw&ₚ (Raw×ₚ RawPublicKey RawOctetStringValue)
                      (Raw&ₚ (RawOption (RawTLV _ RawBitStringValue))
                      (Raw&ₚ (RawOption (RawTLV _ RawBitStringValue))
                             (RawOption RawExtensions))))))))

RawTBSCertFields : Raw TBSCertFields
RawTBSCertFields = Iso.raw equivalentTBSCertFields RawTBSCertFieldsRep

RawTBSCert : Raw TBSCert
RawTBSCert = RawTLV _ RawTBSCertFields
