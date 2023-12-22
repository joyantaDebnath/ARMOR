open import Armor.Binary
open import Armor.Data.X509.PublicKey.Alg.ECPKParameters.ECParameters.Curve.TCB
  hiding (equivalent)
open import Armor.Data.X509.PublicKey.Alg.ECPKParameters.ECParameters.FieldID.TCB
open import Armor.Data.X690-DER.Int.TCB
open import Armor.Data.X690-DER.OID.TCB
open import Armor.Data.X690-DER.OctetString.TCB
open import Armor.Data.X690-DER.TLV.TCB
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Definitions.Iso
import      Armor.Grammar.Definitions.NonMalleable
import      Armor.Grammar.Option.TCB
import      Armor.Grammar.Seq.TCB
open import Armor.Prelude
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Armor.Data.X509.PublicKey.Alg.ECPKParameters.ECParameters.TCB where

open Armor.Grammar.Definitions.Iso          UInt8
open Armor.Grammar.Definitions.NonMalleable UInt8
open Armor.Grammar.Option.TCB               UInt8
open Armor.Grammar.Seq.TCB                  UInt8

{- https://datatracker.ietf.org/doc/html/rfc3279#section-2.3.5
-- ECParameters ::= SEQUENCE {
--    version   ECPVer,          -- version is always 1
--    fieldID   FieldID,         -- identifies the finite field over
--                               -- which the curve is defined
--    curve     Curve,           -- coefficients a and b of the
--                               -- elliptic curve
--    base      ECPoint,         -- specifies the base point P
--                               -- on the elliptic curve
--    order     INTEGER,         -- the order n of the base point
--    cofactor  INTEGER OPTIONAL -- The integer h = #E(Fq)/n
--    }
-- 
-- ECPVer ::= INTEGER {ecpVer1(1)}
--
-- ECPoint ::= OCTET STRING
-- The components of type ECParameters have the following meanings:
--
--    version specifies the version number of the elliptic curve
--    parameters.  It MUST have the value 1 (ecpVer1).
--
--    fieldID identifies the finite field over which the elliptic curve
--    is defined.  Finite fields are represented by values of the
--    parameterized type FieldID, constrained to the values of the
--    objects defined in the information object set FieldTypes.
--    Additional detail regarding fieldID is provided below.
--
--    curve specifies the coefficients a and b of the elliptic curve E.
--    Each coefficient is represented as a value of type FieldElement,
--    an OCTET STRING. seed is an optional parameter used to derive the
--    coefficients of a randomly generated elliptic curve.
--
--    base specifies the base point P on the elliptic curve.  The base
--    point is represented as a value of type ECPoint, an OCTET STRING.
--
--    order specifies the order n of the base point.
--
--    cofactor is the integer h = #E(Fq)/n.  This parameter is specified
--    as OPTIONAL.  However, the cofactor MUST be included in ECDH
--    public key parameters.  The cofactor is not required to support
--    ECDSA, except in parameter validation.  The cofactor MAY be
--    included to support parameter validation for ECDSA keys.
--    Parameter validation is not required by this specification.
-}

record ECParametersFields (@0 bs : List UInt8) : Set where
  constructor mkECParametersFields
  field
    @0 {f c b o cf} : List UInt8
    version : Singleton (# 2 ∷ # 1 ∷ [ # 1 ])
    fieldID : FieldID f
    curve : Curve c
    base : OctetString b
    order : Int o
    cofactor : Option Int cf
    @0 bs≡  : bs ≡ Singleton.x version ++ f ++ c ++ b ++ o ++ cf

ECParametersFieldsRep : @0 List UInt8 → Set
ECParametersFieldsRep =
  &ₚ (λ x → Erased (x ≡ # 2 ∷ # 1 ∷ [ # 1 ])) (&ₚ FieldID (&ₚ Curve (&ₚ OctetString (&ₚ Int (Option Int)))))

equivalent : Equivalent ECParametersFieldsRep ECParametersFields
proj₁ equivalent (mk&ₚ (─ refl) (mk&ₚ fieldID (mk&ₚ curve (mk&ₚ base (mk&ₚ order cofactor refl) refl) refl) refl) refl) =
  mkECParametersFields self fieldID curve base order cofactor refl
proj₂ equivalent (mkECParametersFields self fieldID curve base order cofactor refl) =
  mk&ₚ (─ refl) (mk&ₚ fieldID (mk&ₚ curve (mk&ₚ base (mk&ₚ order cofactor refl) refl) refl) refl) refl

RawECParametersFieldsRep : Raw ECParametersFieldsRep
RawECParametersFieldsRep =
  Raw&ₚ RawSubSingleton (Raw&ₚ RawFieldID (Raw&ₚ RawCurve (Raw&ₚ RawOctetString (Raw&ₚ RawInt (RawOption RawInt)))))

RawECParametersFields : Raw ECParametersFields
RawECParametersFields = Iso.raw equivalent RawECParametersFieldsRep

ECParameters : @0 List UInt8 → Set
ECParameters = TLV Tag.Sequence ECParametersFields

RawECParameters : Raw ECParameters
RawECParameters = RawTLV _ RawECParametersFields
