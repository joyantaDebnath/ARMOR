open import Armor.Binary
open import Armor.Data.X690-DER.BitString.TCB
open import Armor.Data.X690-DER.OctetString.TCB
open import Armor.Data.X690-DER.TLV.TCB
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Definitions.Iso
import      Armor.Grammar.Definitions.NonMalleable
import      Armor.Grammar.Seq.TCB
import      Armor.Grammar.Option.TCB
open import Armor.Prelude

module Armor.Data.X509.PublicKey.Alg.ECPKParameters.ECParameters.Curve.TCB where

open Armor.Grammar.Definitions.Iso          UInt8
open Armor.Grammar.Definitions.NonMalleable UInt8
open Armor.Grammar.Option.TCB UInt8
open Armor.Grammar.Seq.TCB                  UInt8

open ≡-Reasoning

{- https://datatracker.ietf.org/doc/html/rfc3279#section-2.3.5
-- 
-- Curve ::= SEQUENCE {
--    a         FieldElement,
--    b         FieldElement,
--    seed      BIT STRING OPTIONAL }
--
-- FieldElement ::= OCTET STRING
--
-- The value of FieldElement SHALL be the octet string representation of
-- a field element following the conversion routine in [X9.62], Section
-- 4.3.3.
--
-- The components of type ECParameters have the following meanings:
-- [...]
--     curve specifies the coefficients a and b of the elliptic curve E.
--     Each coefficient is represented as a value of type FieldElement,
--     an OCTET STRING. seed is an optional parameter used to derive the
--     coefficients of a randomly generated elliptic curve.
-}

-- Not interpreted
FieldElement = OctetString

record CurveFields (@0 bs : List UInt8) : Set where
  constructor mkCurveFields
  field
    @0 {p q r} : List UInt8
    a : FieldElement p
    b : FieldElement q
    seed : Option BitString r
    @0 bs≡  : bs ≡ p ++ q ++ r

CurveFieldsRep : @0 List UInt8 → Set
CurveFieldsRep = &ₚ (&ₚ OctetString OctetString) (Option BitString)

equivalent : Equivalent CurveFieldsRep CurveFields
proj₁ equivalent (mk&ₚ (mk&ₚ{bs₁}{bs₂} fstₚ₁ sndₚ₂ refl) sndₚ₁ bs≡) = mkCurveFields fstₚ₁ sndₚ₂ sndₚ₁
  (begin (_ ≡⟨ bs≡ ⟩ ++-assoc bs₁ bs₂ _))
proj₂ equivalent (mkCurveFields{p}{q} a b seed bs≡) = mk&ₚ (mk&ₚ a b refl) seed
  (begin (_ ≡⟨ bs≡ ⟩ sym (++-assoc p q _)))

RawCurveFieldsRep : Raw CurveFieldsRep
RawCurveFieldsRep = Raw&ₚ (Raw&ₚ RawOctetString RawOctetString) (RawOption RawBitString)

RawCurveFields : Raw CurveFields
RawCurveFields = Iso.raw equivalent RawCurveFieldsRep

Curve : @0 List UInt8 → Set
Curve xs = TLV Tag.Sequence CurveFields xs

RawCurve : Raw Curve
RawCurve = RawTLV _ RawCurveFields
