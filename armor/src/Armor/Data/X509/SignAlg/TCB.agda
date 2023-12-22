open import Armor.Binary
open import Armor.Data.X690-DER.OctetString.TCB
open import Armor.Data.X690-DER.OID
open import Armor.Data.X690-DER.OctetString.TCB
open import Armor.Data.X690-DER.Sequence.DefinedByOID.TCB
  hiding (equivalent)
open import Armor.Data.X690-DER.TLV.TCB
open import Armor.Data.X509.HashAlg.RFC4055.TCB
import      Armor.Data.X509.SignAlg.TCB.OIDs as OIDs
import      Armor.Data.X509.SignAlg.ECDSA.TCB as ECDSA
import      Armor.Data.X509.SignAlg.DSA.TCB   as DSA
import      Armor.Data.X509.SignAlg.RSA.TCB   as RSA
import      Armor.Grammar.Sum.TCB
import      Armor.Grammar.Definitions
open import Armor.Prelude
import      Data.List.Relation.Unary.Any.Properties as Any
open import Data.Sum as Sum

open Armor.Grammar.Definitions              UInt8
open Armor.Grammar.Sum.TCB                  UInt8

module Armor.Data.X509.SignAlg.TCB where

{- https://datatracker.ietf.org/doc/html/rfc5280#section-4.1.1.2
--
-- The signatureAlgorithm field contains the identifier for the
-- cryptographic algorithm used by the CA to sign this certificate.
-- [RFC3279], [RFC4055], and [RFC4491] list supported signature
-- algorithms, but other signature algorithms MAY also be supported.
--
-- An algorithm identifier is defined by the following ASN.1 structure:
--
-- AlgorithmIdentifier  ::=  SEQUENCE  {
--      algorithm               OBJECT IDENTIFIER,
--      parameters              ANY DEFINED BY algorithm OPTIONAL  }
--
-- The algorithm identifier is used to identify a cryptographic
-- algorithm.  The OBJECT IDENTIFIER component identifies the algorithm
-- (such as DSA with SHA-1).  The contents of the optional parameters
-- field will vary according to the algorithm identified.
--
-- This field MUST contain the same algorithm identifier as the
-- signature field in the sequence tbsCertificate (Section 4.1.2.3).
-}

LookupSignAlg : ∀ {@0 bs} → (o : OID bs) → Set
LookupSignAlg o =
    (-, TLV.val o) ∈ OIDs.DSA.Supported
  ⊎ (-, TLV.val o) ∈ OIDs.ECDSA.Supported
  ⊎ (-, TLV.val o) ∈ OIDs.RSA.Supported

lookupSignAlg : ∀ {@0 bs} → (o : OID bs) → (-, TLV.val o) ∈ OIDs.Supported → LookupSignAlg o
lookupSignAlg o o∈ = Sum.map₂ (Any.++⁻ OIDs.ECDSA.Supported) (Any.++⁻ OIDs.DSA.Supported o∈)

SignAlgParam“ : ∀ {@0 bs} → (o : OID bs) → LookupSignAlg o → @0 List UInt8 → Set
SignAlgParam“ o (inj₁ x)        = DSA.DSAParams' o (yes x)
SignAlgParam“ o (inj₂ (inj₁ x)) = ECDSA.ECDSAParams' o (yes x)
SignAlgParam“ o (inj₂ (inj₂ y)) = RSA.RSAParams' o (yes y)

SignAlgParam' : ∀ {@0 bs} → (o : OID bs) (o∈? : Dec ((-, TLV.val o) ∈ OIDs.Supported))
               → @0 List UInt8 → Set
SignAlgParam' o (no ¬p) = OctetStringValue
SignAlgParam' o (yes p) = SignAlgParam“ o (lookupSignAlg o p)

isSupported : ∀ {@0 bs} → (o : OID bs) → Dec ((-, TLV.val o) ∈ OIDs.Supported)
isSupported o = (-, TLV.val o) ∈? OIDs.Supported

SignAlgParam : AnyDefinedByOID
SignAlgParam o = SignAlgParam' o (isSupported o)

RawSignAlgParamRep : Raw _
RawSignAlgParamRep =
   RawSum RawOctetStringValue
  (RawSum DSA.RawDSAParamsRep
  (RawSum ECDSA.RawECDSAParamsRep
          RSA.RawRSAParamsRep))

RawSignAlgParam : Raw₁ RawOID SignAlgParam
toRawSignAlgParam' : ∀ {@0 bs} → (o : OID bs) → (o∈? : Dec ((-, TLV.val o) ∈ OIDs.Supported))
                     → ∀ {@0 bs'} → SignAlgParam' o o∈? bs' → Raw₁.D RawSignAlgParam (Raw.to RawOID o)
toRawSignAlgParam“ : ∀ {@0 bs} → (o : OID bs) → (o∈? : LookupSignAlg o)
                     → ∀ {@0 bs'} → SignAlgParam“ o o∈? bs' → Raw₁.D RawSignAlgParam (Raw.to RawOID o)

Raw₁.D RawSignAlgParam o = Raw.D RawSignAlgParamRep
Raw₁.to RawSignAlgParam o = toRawSignAlgParam' o (isSupported o)

toRawSignAlgParam' o (no ¬p) p = Raw.to RawSignAlgParamRep (inj₁ p)
toRawSignAlgParam' o (yes p) p' = toRawSignAlgParam“ o (lookupSignAlg o p) p'

toRawSignAlgParam“ o (inj₁ x) p = Raw.to RawSignAlgParamRep (inj₂ (inj₁ p))
toRawSignAlgParam“ o (inj₂ (inj₁ x)) p = Raw.to RawSignAlgParamRep (inj₂ (inj₂ (inj₁ p)))
toRawSignAlgParam“ o (inj₂ (inj₂ y)) p = inj₂ (inj₂ (inj₂ (RSA.toRawRSAParams' o (yes y) p)))

SignAlg : @0 List UInt8 → Set
SignAlg = DefinedByOID SignAlgParam

RawSignAlg : Raw SignAlg
RawSignAlg = RawDefinedByOID RawSignAlgParam

getOID : ∀ {@0 bs} → (s : SignAlg bs) → OID _
getOID s = DefinedByOIDFields.oid (TLV.val s)

getOIDBS : ∀ {@0 bs} → SignAlg bs → List UInt8
getOIDBS = ↑_ ∘ OID.serialize ∘ getOID

-- proj₁ equivalent (Armor.Grammar.Sum.TCB.inj₁ (mkTLV len val len≡ refl)) = {!!}
-- proj₁ equivalent (Armor.Grammar.Sum.TCB.inj₂ (Armor.Grammar.Sum.TCB.inj₁ x)) = {!!}
-- proj₁ equivalent (Armor.Grammar.Sum.TCB.inj₂ (Armor.Grammar.Sum.TCB.inj₂ x)) = {!!}
-- proj₂ equivalent (mkOIDDefinedFields oid param bs≡) = {!!}
  -- case (-, TLV.val oid) ∈? OIDs.Supported
  -- of λ where
  --   (no ¬p) → {!!}
  --   (yes p) →
  --     case lookupSignAlg oid p
  --     of λ where
  --       (inj₁ x) → inj₁ {!!}
  --       (inj₂ (inj₁ x)) → inj₂ (inj₁ {!!})
  --       (inj₂ (inj₂ y)) → inj₂ (inj₂ {!!})
