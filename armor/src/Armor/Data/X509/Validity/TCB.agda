open import Armor.Binary
open import Armor.Data.X509.Validity.Time.Ordering
open import Armor.Data.X509.Validity.Time.TCB
  hiding (equivalent)
open import Armor.Data.X690-DER.TLV.TCB
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Definitions.Iso
import      Armor.Grammar.Definitions.NonMalleable.Base
import      Armor.Grammar.Seq.TCB
open import Armor.Prelude

module Armor.Data.X509.Validity.TCB where

open Armor.Grammar.Definitions.Iso UInt8
open Armor.Grammar.Definitions.NonMalleable.Base UInt8
open Armor.Grammar.Seq.TCB UInt8

-- https://datatracker.ietf.org/doc/html/rfc5280#section-4.1
--    Validity ::= SEQUENCE {
--         notBefore      Time,
--         notAfter       Time }

   -- The certificate validity period is the time interval during which the
   -- CA warrants that it will maintain information about the status of the
   -- certificate.  The field is represented as a SEQUENCE of two dates:
   -- the date on which the certificate validity period begins (notBefore)
   -- and the date on which the certificate validity period ends
   -- (notAfter).  Both notBefore and notAfter may be encoded as UTCTime or
   -- GeneralizedTime.

   -- CAs conforming to this profile MUST always encode certificate
   -- validity dates through the year 2049 as UTCTime; certificate validity
   -- dates in 2050 or later MUST be encoded as GeneralizedTime.
   -- Conforming applications MUST be able to process validity dates that
   -- are encoded in either UTCTime or GeneralizedTime.

   -- The validity period for a certificate is the period of time from
   -- notBefore through notAfter, inclusive.
   
record ValidityFields (@0 bs : List UInt8) : Set where
  constructor mkValidityFields
  field
    @0 {nb na} : List UInt8
    start : Time nb
    end : Time na
    @0 bs≡  : bs ≡ nb ++ na

ValidityFieldsRep : @0 List UInt8 → Set
ValidityFieldsRep = &ₚ Time Time

equivalent : Equivalent ValidityFieldsRep ValidityFields
proj₁ equivalent (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = mkValidityFields fstₚ₁ sndₚ₁ bs≡
proj₂ equivalent (mkValidityFields start end bs≡) = mk&ₚ start end bs≡

RawValidityFieldsRep : Raw ValidityFieldsRep
RawValidityFieldsRep = Raw&ₚ RawTime RawTime

RawValidityFields : Raw ValidityFields
RawValidityFields = Iso.raw equivalent RawValidityFieldsRep

Validity : @0 List UInt8 → Set
Validity = TLV Tag.Sequence ValidityFields

RawValidity : Raw Validity
RawValidity = RawTLV _ RawValidityFields

getNBTime : ∀ {@0 bs} → (v : Validity bs) → Time (ValidityFields.nb (TLV.val v))
getNBTime v = ValidityFields.start (TLV.val v)

getNATime : ∀ {@0 bs} → (v : Validity bs) → Time (ValidityFields.na (TLV.val v))
getNATime v = ValidityFields.end (TLV.val v)

ValidTime : {@0 bs₁ bs₂ : List UInt8} → Time bs₁ → Validity bs₂ → Set
ValidTime t v = getNBTime v Time≤ t × t Time≤ getNATime v

validTime? : ∀ {@0 bs₁ bs₂} → (t : Time bs₁) (v : Validity bs₂) → Dec (ValidTime t v)
validTime? t v = (getNBTime v Time≤? t) ×-dec (t Time≤? getNATime v)
