open import Armor.Binary
open import Armor.Data.X690-DER.Null.TCB
open import Armor.Data.X690-DER.OID
open import Armor.Data.X690-DER.Sequence.DefinedByOID.TCB
open import Armor.Data.X690-DER.TLV.TCB
open import Armor.Data.X690-DER.OctetString.TCB
import      Armor.Data.X690-DER.Tag as Tag
-- open import Armor.Data.X509.SignAlg.RSA.PSS.TCB
open import Armor.Data.X509.SignAlg.TCB.OIDs  as OIDs
import      Armor.Data.X509.HashAlg.RFC4055   as HashAlg
import      Armor.Data.X509.HashAlg.TCB.OIDs  as OIDs
import      Armor.Grammar.Definitions
import      Armor.Grammar.Option.TCB
import      Armor.Grammar.Parallel.TCB
import      Armor.Grammar.Sum.TCB
open import Armor.Prelude
import      Data.Sum as Sum

module Armor.Data.X509.SignAlg.RSA.TCB where

open Armor.Grammar.Definitions  UInt8
open Armor.Grammar.Option.TCB   UInt8
open Armor.Grammar.Parallel.TCB UInt8
open Armor.Grammar.Sum.TCB      UInt8

{-
https://datatracker.ietf.org/doc/html/rfc3279#section-2.2

The signature algorithm with MD2 and the RSA encryption algorithm is
defined in PKCS #1 [RFC 2313].  As defined in PKCS #1 [RFC 2313], the
ASN.1 OID used to identify this signature algorithm is:

   md2WithRSAEncryption OBJECT IDENTIFIER  ::=  {
       iso(1) member-body(2) us(840) rsadsi(113549) pkcs(1)
       pkcs-1(1) 2  }

The signature algorithm with MD5 and the RSA encryption algorithm is
defined in PKCS #1 [RFC 2313].  As defined in PKCS #1 [RFC 2313], the
ASN.1 OID used to identify this signature algorithm is:

    md5WithRSAEncryption OBJECT IDENTIFIER  ::=  {
        iso(1) member-body(2) us(840) rsadsi(113549) pkcs(1)
        pkcs-1(1) 4  }

The ASN.1 object identifier used to identify this signature algorithm
is:

      sha-1WithRSAEncryption OBJECT IDENTIFIER  ::=  {
          iso(1) member-body(2) us(840) rsadsi(113549) pkcs(1)
          pkcs-1(1) 5  }

When any of these three OIDs appears within the ASN.1 type
AlgorithmIdentifier, the parameters component of that type SHALL be
the ASN.1 type NULL.
-}

{-
https://datatracker.ietf.org/doc/html/rfc4055#section-5

The object identifier used to identify the PKCS #1 version 1.5
   signature algorithm with SHA-224 is:

      sha224WithRSAEncryption  OBJECT IDENTIFIER  ::=  { pkcs-1 14 }

   The object identifier used to identify the PKCS #1 version 1.5
   signature algorithm with SHA-256 is:

      sha256WithRSAEncryption  OBJECT IDENTIFIER  ::=  { pkcs-1 11 }

   The object identifier used to identify the PKCS #1 version 1.5
   signature algorithm with SHA-384 is:

      sha384WithRSAEncryption  OBJECT IDENTIFIER  ::=  { pkcs-1 12 }

   The object identifier used to identify the PKCS #1 version 1.5
   signature algorithm with SHA-512 is:

      sha512WithRSAEncryption  OBJECT IDENTIFIER  ::=  { pkcs-1 13 }

   When any of these four object identifiers appears within an
   AlgorithmIdentifier, the parameters MUST be NULL.  Implementations
   MUST accept the parameters being absent as well as present.

-}

{-
https://datatracker.ietf.org/doc/html/rfc4055#section-3.1

When RSASSA-PSS is used in an AlgorithmIdentifier, the parameters
MUST employ the RSASSA-PSS-params syntax.  The parameters may be
either absent or present when used as subject public key information.
The parameters MUST be present when used in the algorithm identifier
associated with a signature value.

When signing, it is RECOMMENDED that the parameters, except for
possibly saltLength, remain fixed for all usages of a given RSA key
pair.

  id-RSASSA-PSS  OBJECT IDENTIFIER  ::=  { pkcs-1 10 }
-}

SplitRSA∈ : ∀ {@0 bs} (o : OID bs) → Set
SplitRSA∈ o =   (-, TLV.val o) ∈ OIDs.RSA.ExplicitNullParam
              ⊎ (-, TLV.val o) ∈ OIDs.RSA.ExplicitOrImplicitNullParam
              ⊎ (-, TLV.val o) ∈ [ Exists─ _ OIDValue ∋ -, OIDs.RSA.PSS ]

splitRSA∈ : ∀ {@0 bs} (o : OID bs) → (-, TLV.val o) ∈ OIDs.RSA.Supported → SplitRSA∈ o
splitRSA∈ o o∈? = Sum.map₂ (Any.++⁻ OIDs.RSA.ExplicitOrImplicitNullParam) (Any.++⁻ OIDs.RSA.ExplicitNullParam o∈?)

RSAParams“ : ∀ {@0 bs} → (o : OID bs) → SplitRSA∈ o → @0 List UInt8 → Set

RSAParams“ o (inj₁ x) = Null
RSAParams“ o (inj₂ (inj₁ x)) = Option Null
RSAParams“ o (inj₂ (inj₂ y)) = TLV Tag.Sequence OctetStringValue --PSSParamSeq

RSAParamsRep : @0 List UInt8 → Set
RSAParamsRep = Sum Null (Sum (Option Null) (TLV Tag.Sequence OctetStringValue)) --PSSParamSeq))

RawRSAParamsRep : Raw RSAParamsRep
RawRSAParamsRep = RawSum RawNull (RawSum (RawOption RawNull) (RawTLV _ RawOctetStringValue)) --RawPSSParamSeq))

RSAParams' : ∀ {@0 bs} → (o : OID bs) → Dec ((-, TLV.val o) ∈ OIDs.RSA.Supported) → @0 List UInt8 → Set
RSAParams' o (no ¬p) bs = ⊥
RSAParams' o (yes p) bs = RSAParams“ o (splitRSA∈ o p) bs

RSAParams : AnyDefinedByOID
RSAParams o = RSAParams' o ((-, TLV.val o) ∈? OIDs.RSA.Supported)

RawRSAParams : Raw₁ RawOID RSAParams
toRawRSAParams' : ∀ {@0 bs} → (o : OID bs) (o∈? : Dec ((-, TLV.val o) ∈ OIDs.RSA.Supported))
                → ∀ {@0 bs'} → RSAParams' o o∈? bs' → Raw₁.D RawRSAParams (Raw.to RawOID o)
toRawRSAParams“ : ∀ {@0 bs} → (o : OID bs) (o∈? : SplitRSA∈ o)
                → ∀ {@0 bs'} → RSAParams“ o o∈? bs' → Raw₁.D RawRSAParams (Raw.to RawOID o)

Raw₁.D RawRSAParams o = Raw.D RawRSAParamsRep
Raw₁.to RawRSAParams o = toRawRSAParams' o ((-, TLV.val o) ∈? OIDs.RSA.Supported)

toRawRSAParams' o (yes p₁) = toRawRSAParams“ o (splitRSA∈ o p₁)
toRawRSAParams“ o (inj₁ x) p = Raw.to RawRSAParamsRep (inj₁ p)
toRawRSAParams“ o (inj₂ (inj₁ x)) p = Raw.to RawRSAParamsRep (inj₂ (inj₁ p))
toRawRSAParams“ o (inj₂ (inj₂ y)) p = Raw.to RawRSAParamsRep (inj₂ (inj₂ p))

RSA : @0 List UInt8 → Set
RSA = DefinedByOID RSAParams

RawRSA : Raw RSA
RawRSA = RawDefinedByOID RawRSAParams

getOID : ∀ {@0 bs} → (r : RSA bs) → OID _
getOID s = DefinedByOIDFields.oid (TLV.val s)
