open import Armor.Binary
open import Armor.Data.X509.PublicKey.Alg.ECPKParameters.ECParameters.TCB
  hiding (equivalent)
open import Armor.Data.X690-DER.Null.TCB
open import Armor.Data.X690-DER.OID.TCB
import      Armor.Grammar.Definitions.Iso
import      Armor.Grammar.Definitions.NonMalleable
import      Armor.Grammar.Sum.TCB
open import Armor.Prelude

module Armor.Data.X509.PublicKey.Alg.ECPKParameters.TCB where

open Armor.Grammar.Definitions.Iso          UInt8
open Armor.Grammar.Definitions.NonMalleable UInt8
open Armor.Grammar.Sum.TCB                  UInt8

{- https://datatracker.ietf.org/doc/html/rfc3279#section-2.3.5
-- ECDSA and ECDH require use of certain parameters with the public key.
-- The parameters may be inherited from the issuer, implicitly included
-- through reference to a "named curve," or explicitly included in the
-- certificate.
--
--    EcpkParameters ::= CHOICE {
--      ecParameters  ECParameters,
--      namedCurve    OBJECT IDENTIFIER,
--      implicitlyCA  NULL }
-}

data ECPKParameters : @0 List UInt8 → Set where
  ecparams     : ∀ {@0 bs} → ECParameters bs → ECPKParameters bs
  namedcurve   : ∀ {@0 bs} → OID bs          → ECPKParameters bs
  implicitlyCA : ∀ {@0 bs} → Null bs         → ECPKParameters bs

ECPKParametersRep : @0 List UInt8 → Set
ECPKParametersRep =
  Sum ECParameters (Sum OID Null)

equivalent : Equivalent ECPKParametersRep ECPKParameters
proj₁ equivalent (inj₁ x) = ecparams x
proj₁ equivalent (inj₂ (inj₁ x)) = namedcurve x
proj₁ equivalent (inj₂ (inj₂ x)) = implicitlyCA x
proj₂ equivalent (ecparams x) = inj₁ x
proj₂ equivalent (namedcurve x) = inj₂ (inj₁ x)
proj₂ equivalent (implicitlyCA x) = inj₂ (inj₂ x)

RawECPKParametersRep : Raw ECPKParametersRep
RawECPKParametersRep = RawSum RawECParameters (RawSum RawOID RawNull)

RawECPKParameters : Raw ECPKParameters
RawECPKParameters = Iso.raw equivalent RawECPKParametersRep
