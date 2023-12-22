open import Armor.Binary
open import Armor.Data.X690-DER.Int.TCB as Int
  hiding (getVal)
open import Armor.Data.X690-DER.Length.TCB
open import Armor.Data.X690-DER.TLV.TCB
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Definitions.NonMalleable
import      Armor.Grammar.Parallel.TCB
open import Armor.Prelude

module Armor.Data.X509.TBSCert.Version.TCB where

open Armor.Grammar.Definitions.NonMalleable UInt8
open Armor.Grammar.Parallel.TCB             UInt8

{- https://datatracker.ietf.org/doc/html/rfc5280#section-4.1
--
-- TBSCertificate  ::=  SEQUENCE  {
--      version         [0]  EXPLICIT Version DEFAULT v1,
--      serialNumber         CertificateSerialNumber,
--      signature            AlgorithmIdentifier,
--      issuer               Name,
--      validity             Validity,
--      subject              Name,
--      subjectPublicKeyInfo SubjectPublicKeyInfo,
--      issuerUniqueID  [1]  IMPLICIT UniqueIdentifier OPTIONAL,
--                           -- If present, version MUST be v2 or v3
--      subjectUniqueID [2]  IMPLICIT UniqueIdentifier OPTIONAL,
--                           -- If present, version MUST be v2 or v3
--      extensions      [3]  EXPLICIT Extensions OPTIONAL
--                           -- If present, version MUST be v3
--      }
--
-- Version  ::=  INTEGER  {  v1(0), v2(1), v3(2)  }
-}

data DecodedVersion : Set where
  v1 v2 v3 : DecodedVersion

supportedVersions : List ℤ
supportedVersions = ℤ.+ 0 ∷ ℤ.+ 1 ∷ [ ℤ.+ 2 ]

Version : @0 List UInt8 → Set
Version = Σₚ Int λ _ i → Erased (Int.getVal i ∈ supportedVersions)

mkVersion : (i : Fin 3) → Version (Tag.Integer ∷ # 1 ∷ [ Fin.inject≤ i _ ])
mkVersion i =
  mk×ₚ (mkInt i) 
    (─ (case i ret (λ x → Int.getVal (mkInt x) ∈ supportedVersions) of λ where
      Fin.zero → here refl
      (Fin.suc Fin.zero) → there (here refl)
      (Fin.suc (Fin.suc Fin.zero)) → there (there (here refl))))
  where
  mkInt : (i : Fin 3) → Int (Tag.Integer ∷ # 1 ∷ [ Fin.inject≤ i _ ])
  mkInt i =
    mkTLV
      (short (mkShort (# 1) (toWitness{Q = _ <? _} tt) refl))
      (mkIntVal (Fin.inject≤ i (s≤s (s≤s (s≤s z≤n)))) [] tt self refl)
      refl refl

v1Version = mkVersion (# 0)
v2Version = mkVersion (# 1)
v3Version = mkVersion (# 2)

RawVersion : Raw Version
toRawVersion : ∀ {@0 bs} → (@0 i : Int bs) (i∈ : Int.getVal i ∈ supportedVersions) → DecodedVersion
Raw.D RawVersion = DecodedVersion
Raw.to RawVersion (mk×ₚ i (─ i∈)) = toRawVersion i (uneraseDec i∈ (_ ∈? _))

toRawVersion i (here px) = v1
toRawVersion i (there (here px)) = v2
toRawVersion i (there (there (here px))) = v3

[0]ExplicitVersion : @0 List UInt8 → Set
[0]ExplicitVersion = TLV Tag.AA0 Version

v1[0]ExplicitVersion : [0]ExplicitVersion _
v1[0]ExplicitVersion = mkTLV (short (mkShort (# 3) (toWitness{Q = _ <? _} tt) refl)) v1Version refl refl

Raw[0]ExplicitVersion : Raw [0]ExplicitVersion
Raw[0]ExplicitVersion = RawTLV _ RawVersion

getVersion : ∀ {@0 bs} → [0]ExplicitVersion bs → DecodedVersion
getVersion v = Raw.to Raw[0]ExplicitVersion v
