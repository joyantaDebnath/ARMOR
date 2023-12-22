open import Armor.Binary
open import Armor.Data.X509.Extension.TCB
import      Armor.Data.X509.Extension.BC.TCB as BC
open import Armor.Data.X509.Name.TCB
open import Armor.Data.X509.SignAlg.TCB
open import Armor.Data.X509.TBSCert.TCB
open import Armor.Data.X509.TBSCert.Version.TCB
  using (DecodedVersion)
import      Armor.Data.X509.TBSCert.UID.TCB as TBSCert
open import Armor.Data.X509.Validity.TCB
open import Armor.Data.X509.Validity.Time.TCB
import      Armor.Data.X690-DER.BitString.Serializer as BitString
open import Armor.Data.X690-DER.BitString.TCB
open import Armor.Data.X690-DER.OctetString.TCB
open import Armor.Data.X690-DER.Int.TCB
open import Armor.Data.X690-DER.TLV.TCB
import      Armor.Data.X690-DER.Tag as Tag
open import Armor.Data.X690-DER.SequenceOf
open import Armor.Data.X690-DER.OID
import      Armor.Grammar.IList.TCB
import      Armor.Grammar.Option.TCB
import      Armor.Grammar.Parallel.TCB
import      Armor.Grammar.Definitions
import      Armor.Grammar.Seq
open import Armor.Prelude

module Armor.Data.X509.Cert.TCB where

open Armor.Grammar.Seq    UInt8
open Armor.Grammar.IList.TCB    UInt8
open Armor.Grammar.Option.TCB   UInt8
open Armor.Grammar.Parallel.TCB UInt8
open Armor.Grammar.Definitions UInt8

-- https://datatracker.ietf.org/doc/html/rfc5280#section-4.1
--    Certificate  ::=  SEQUENCE  {
--         tbsCertificate       TBSCertificate,
--         signatureAlgorithm   AlgorithmIdentifier,
--         signatureValue       BIT STRING  }
        
record CertFields (@0 bs : List UInt8) : Set where
  constructor mkCertFields
  field
    @0 {t sa sig} : List UInt8
    tbs : TBSCert t
    tbsBytes : Singleton t    -- TODO: eventually this should come from serialization
    signAlg : SignAlg sa
    signature : BitString sig
    signatureBytes : Singleton sig
    @0 bs≡  : bs ≡ t ++ sa ++ sig

  getVersion : DecodedVersion
  getVersion = TBSCertFields.getVersion (TLV.val tbs)

  getSerial : ℤ
  getSerial = TBSCertFields.getSerial (TLV.val tbs)

  getValidity : Validity _
  getValidity = TBSCertFields.validity (TLV.val tbs)

  getValidityStartTime : Time _
  getValidityEndTime   : Time _

  getValidityStartTime = TBSCertFields.getValidityStartTime ∘ TLV.val $ tbs
  getValidityEndTime   = TBSCertFields.getValidityEndTime  ∘ TLV.val $ tbs 

  -- getYearNB :  ℕ
  -- getYearNB = TBSCertFields.getYearNB (TLV.val tbs)
  -- getMonthNB :  ℕ
  -- getMonthNB = TBSCertFields.getMonthNB (TLV.val tbs)
  -- getDayNB :  ℕ
  -- getDayNB = TBSCertFields.getDayNB (TLV.val tbs)
  -- getHourNB :  ℕ
  -- getHourNB = TBSCertFields.getHourNB (TLV.val tbs)
  -- getMinNB :  ℕ
  -- getMinNB = TBSCertFields.getMinNB (TLV.val tbs)
  -- getSecNB :  ℕ
  -- getSecNB = TBSCertFields.getSecNB (TLV.val tbs)

  -- getYearNA :  ℕ
  -- getYearNA = TBSCertFields.getYearNA (TLV.val tbs)
  -- getMonthNA :  ℕ
  -- getMonthNA = TBSCertFields.getMonthNA (TLV.val tbs)
  -- getDayNA :  ℕ
  -- getDayNA = TBSCertFields.getDayNA (TLV.val tbs)
  -- getHourNA :  ℕ
  -- getHourNA = TBSCertFields.getHourNA (TLV.val tbs)
  -- getMinNA :  ℕ
  -- getMinNA = TBSCertFields.getMinNA (TLV.val tbs)
  -- getSecNA :  ℕ
  -- getSecNA = TBSCertFields.getSecNA (TLV.val tbs)

  getIssuerLen :  ℕ
  getIssuerLen = TBSCertFields.getIssuerLen (TLV.val tbs)

  getSubjectLen :  ℕ
  getSubjectLen = TBSCertFields.getSubjectLen (TLV.val tbs)

  getIssuer :  Name _
  getIssuer = TBSCertFields.issuer (TLV.val tbs)

  getSubject :  Name _
  getSubject = TBSCertFields.subject (TLV.val tbs)

  getIssUID : Option TBSCert.IssUID (TBSCertFields.u₁ (TLV.val tbs))
  getIssUID = TBSCertFields.issuerUID (TLV.val tbs)

  getSubUID : Option TBSCert.SubUID (TBSCertFields.u₂ (TLV.val tbs))
  getSubUID = TBSCertFields.subjectUID (TLV.val tbs)

  getTBSCertSignAlg : Exists─ (List UInt8) SignAlg
  getTBSCertSignAlg = TBSCertFields.getSignAlg (TLV.val tbs)

  getCertSignAlg : Exists─ (List UInt8) SignAlg
  getCertSignAlg =  _ , signAlg

  getBC : Exists─ (List UInt8) (Option ExtensionFieldBC)
  getBC = TBSCertFields.getBC (TLV.val tbs)

{- https://datatracker.ietf.org/doc/html/rfc5280#section-6.1.4
--    (k)  If certificate i is a version 3 certificate, verify that the
--         basicConstraints extension is present and that cA is set to
--         TRUE.  (If certificate i is a version 1 or version 2
--         certificate, then the application MUST either verify that
--         certificate i is a CA certificate through out-of-band means
--         or reject the certificate.  Conforming implementations may
--         choose to reject all version 1 and version 2 intermediate
--         certificates.)
-}

  isCA : Maybe Bool
  isCA = elimOption {X = const (Maybe Bool)} nothing (λ bc → just (BC.isCA (ExtensionFields.extension bc))) (proj₂ getBC)

  getKU : Exists─ (List UInt8) (Option ExtensionFieldKU)
  getKU = TBSCertFields.getKU (TLV.val tbs)

  getEKU : Exists─ (List UInt8) (Option ExtensionFieldEKU)
  getEKU = TBSCertFields.getEKU (TLV.val tbs)

  getSAN : Exists─ (List UInt8) (Option ExtensionFieldSAN)
  getSAN = TBSCertFields.getSAN (TLV.val tbs)

  getCRLDIST : Exists─ (List UInt8) (Option ExtensionFieldCRLDist)
  getCRLDIST = TBSCertFields.getCRLDIST (TLV.val tbs)

  getCPOL : Exists─ (List UInt8) (Option ExtensionFieldCPOL)
  getCPOL = TBSCertFields.getCPOL (TLV.val tbs)

  getExtensions : Exists─ (List UInt8) (Option Extensions)
  getExtensions = _ , (TBSCertFields.extensions (TLV.val tbs))
  
  getExtensionsList : List (Exists─ (List UInt8) Extension)
  getExtensionsList = TBSCertFields.getExtensionsList (TLV.val tbs)

  getPublicKeyBytes : List UInt8
  getPublicKeyBytes = ↑ (TBSCertFields.pkBytes (TLV.val tbs))

module Cert where
  Cert : (@0 _ : List UInt8) → Set
  Cert xs = TLV Tag.Sequence  CertFields xs

  module _ {@0 bs} (c : Cert bs) where
    getVersion : DecodedVersion
    getVersion = CertFields.getVersion (TLV.val c)

    getSerial : ℤ
    getSerial = CertFields.getSerial (TLV.val c)

    getTBSBytes : List UInt8
    getTBSBytes = ↑ (CertFields.tbsBytes (TLV.val c))

    getValidity : Validity _
    getValidity = CertFields.getValidity (TLV.val c)

    getValidityStartTime : Time _
    getValidityEndTime   : Time _

    getValidityStartTime = CertFields.getValidityStartTime ∘ TLV.val $ c
    getValidityEndTime   = CertFields.getValidityEndTime   ∘ TLV.val $ c

    -- getYearNB :  ℕ
    -- getYearNB = CertFields.getYearNB (TLV.val c)
    -- getMonthNB :  ℕ
    -- getMonthNB = CertFields.getMonthNB (TLV.val c)
    -- getDayNB :  ℕ
    -- getDayNB = CertFields.getDayNB (TLV.val c)
    -- getHourNB :  ℕ
    -- getHourNB = CertFields.getHourNB (TLV.val c)
    -- getMinNB :  ℕ
    -- getMinNB = CertFields.getMinNB (TLV.val c)
    -- getSecNB :  ℕ
    -- getSecNB = CertFields.getSecNB (TLV.val c)

    -- getYearNA :  ℕ
    -- getYearNA = CertFields.getYearNA (TLV.val c)
    -- getMonthNA :  ℕ
    -- getMonthNA = CertFields.getMonthNA (TLV.val c)
    -- getDayNA :  ℕ
    -- getDayNA = CertFields.getDayNA (TLV.val c)
    -- getHourNA :  ℕ
    -- getHourNA = CertFields.getHourNA (TLV.val c)
    -- getMinNA :  ℕ
    -- getMinNA = CertFields.getMinNA (TLV.val c)
    -- getSecNA :  ℕ
    -- getSecNA = CertFields.getSecNA (TLV.val c)

    getIssuerLen :  ℕ
    getIssuerLen = CertFields.getIssuerLen (TLV.val c)

    getSubjectLen :  ℕ
    getSubjectLen = CertFields.getSubjectLen (TLV.val c)

    getIssuer : Name _
    getIssuer = CertFields.getIssuer (TLV.val c)

    getSubject :  Name _
    getSubject = CertFields.getSubject (TLV.val c)

    getIssUID : Option TBSCert.IssUID (TBSCertFields.u₁ (TLV.val (CertFields.tbs (TLV.val c))))
    getIssUID = CertFields.getIssUID (TLV.val c)

    getSubUID : Option TBSCert.SubUID (TBSCertFields.u₂ (TLV.val (CertFields.tbs (TLV.val c))))
    getSubUID = CertFields.getSubUID (TLV.val c)

    getTBSCertSignAlg : Exists─ (List UInt8) SignAlg
    getTBSCertSignAlg = CertFields.getTBSCertSignAlg (TLV.val c)

    getCertSignAlg : Exists─ (List UInt8) SignAlg
    getCertSignAlg = CertFields.getCertSignAlg (TLV.val c)

    -- getPublicKeyOIDbs : List UInt8
    -- getPublicKeyOIDbs = TBSCertFields.getPublicKeyOIDbs (TLV.val (CertFields.tbs (TLV.val c)))

    getBC : Exists─ (List UInt8) (Option ExtensionFieldBC)
    getBC = CertFields.getBC (TLV.val c)

    isCA : Maybe Bool
    isCA = CertFields.isCA (TLV.val c)

    getKU : Exists─ (List UInt8) (Option ExtensionFieldKU)
    getKU = CertFields.getKU (TLV.val c)

    getEKU : Exists─ (List UInt8) (Option ExtensionFieldEKU)
    getEKU = CertFields.getEKU (TLV.val c)

    getSAN : Exists─ (List UInt8) (Option ExtensionFieldSAN)
    getSAN = CertFields.getSAN (TLV.val c)

    getCRLDIST : Exists─ (List UInt8) (Option ExtensionFieldCRLDist)
    getCRLDIST = CertFields.getCRLDIST (TLV.val c)

    getCPOL : Exists─ (List UInt8) (Option ExtensionFieldCPOL)
    getCPOL = CertFields.getCPOL (TLV.val c)

    getExtensions : Exists─ (List UInt8) (Option Extensions)
    getExtensions = CertFields.getExtensions (TLV.val c)

    getExtensionsList : List (Exists─ (List UInt8) Extension)
    getExtensionsList = CertFields.getExtensionsList (TLV.val c)

    getPublicKeyBytes : List UInt8
    getPublicKeyBytes = CertFields.getPublicKeyBytes (TLV.val c)

    getSignatureBytes : List UInt8
    getSignatureBytes = ↑ CertFields.signatureBytes (TLV.val c)

    getSignatureValueBytes : List UInt8
    getSignatureValueBytes = ↑ (BitString.serializeValue (TLV.val (CertFields.signature (TLV.val c))))

    -- List of EKU OIds to List of List UInt8
    getEKUOIDList : Exists─ (List UInt8) (Option ExtensionFieldEKU) → List (List UInt8)
    getEKUOIDList (─ .[] , none) = []
    getEKUOIDList (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ val len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = helper (fstₚ val)
      where
      helper : ∀ {@0 bs} → SequenceOf OID bs → List (List UInt8)
      helper nil = []
      helper (cons (mkIListCons head₁ tail₁ bs≡)) = (↑ (OID.serialize head₁)) ∷ (helper tail₁)
open Cert public using (Cert)

module CertList where
  CertList : (@0 _ : List UInt8) → Set
  CertList = IList Cert
open CertList public using (CertList)

CertFieldsRep : @0 List UInt8 → Set
CertFieldsRep = &ₚ (TBSCert ×ₚ Singleton) (&ₚ SignAlg (BitString ×ₚ Singleton))

equivalentCertFields : Equivalent CertFieldsRep CertFields
proj₁ equivalentCertFields (mk&ₚ (mk×ₚ fstₚ₁ s) (mk&ₚ fstₚ₂ (mk×ₚ sndₚ₁ s') refl) bs≡) =
  mkCertFields fstₚ₁ s fstₚ₂ sndₚ₁ s' bs≡
proj₂ equivalentCertFields (mkCertFields tbs tbsBytes signAlg signature signatureBytes bs≡)
  = mk&ₚ (mk×ₚ tbs tbsBytes) (mk&ₚ signAlg (mk×ₚ signature signatureBytes) refl) bs≡

RawCertFieldsRep : Raw CertFieldsRep
RawCertFieldsRep = Raw&ₚ (Raw×ₚ RawTBSCert RawOctetStringValue)
                      (Raw&ₚ RawSignAlg (Raw×ₚ RawBitString RawOctetStringValue))

RawCertFields : Raw CertFields
RawCertFields = Iso.raw equivalentCertFields RawCertFieldsRep

RawCert : Raw Cert
RawCert = RawTLV _ RawCertFields

RawCertList : Raw CertList
RawCertList = RawIList RawCert
