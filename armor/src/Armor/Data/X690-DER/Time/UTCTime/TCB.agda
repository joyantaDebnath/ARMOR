open import Armor.Binary
open import Armor.Prelude
open import Armor.Data.X690-DER.TLV.TCB
import      Armor.Data.X690-DER.Tag as Tag
open import Armor.Data.X690-DER.Time.MDHMS.TCB
  hiding (equivalent)
open import Armor.Data.X690-DER.Time.TimeType.TCB
open import Armor.Data.X690-DER.Time.Year.TCB
import      Armor.Grammar.Definitions
import      Armor.Grammar.Seq.TCB

module Armor.Data.X690-DER.Time.UTCTime.TCB where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Seq.TCB     UInt8

-- https://datatracker.ietf.org/doc/html/rfc5280#section-4.1.2.5.1
--    The universal time type, UTCTime, is a standard ASN.1 type intended
--    for representation of dates and time.  UTCTime specifies the year
--    through the two low-order digits and time is specified to the
--    precision of one minute or one second.  UTCTime includes either Z
--    (for Zulu, or Greenwich Mean Time) or a time differential.

--    For the purposes of this profile, UTCTime values MUST be expressed in
--    Greenwich Mean Time (Zulu) and MUST include seconds (i.e., times are
--    YYMMDDHHMMSSZ), even where the number of seconds is zero.  Conforming
--    systems MUST interpret the year field (YY) as follows:

--       Where YY is greater than or equal to 50, the year SHALL be
--       interpreted as 19YY; and

--       Where YY is less than 50, the year SHALL be interpreted as 20YY.
      
record UTCTimeFields (@0 bs : List UInt8) : Set where
  constructor mkUTCTime
  field
    @0 {y m} : List UInt8
    year   : Year₂ y
    mdhms  : MDHMS m
    @0 bs≡ : bs ≡ y ++ m ++ [ # 'Z' ]

  getYear  : Window₂ → ℕ
  getYear w = TimeType.getTime (proj₂ (w year))

  getMonth  = MDHMS.getMonth mdhms
  getDay    = MDHMS.getDay mdhms
  getHour   = MDHMS.getHour mdhms
  getMinute = MDHMS.getMinute mdhms
  getSec    = MDHMS.getSec mdhms

UTCTime : @0 List UInt8 → Set
UTCTime = TLV Tag.UTCTime UTCTimeFields

UTCTimeFieldsRep : @0 List UInt8 → Set
UTCTimeFieldsRep = &ₚ Year₂ (&ₚ MDHMS (λ x → Erased (x ≡ [ # 'Z' ])))

RawUTCTimeFieldsRep : Raw UTCTimeFieldsRep
RawUTCTimeFieldsRep =
   Raw&ₚ RawYear₂
  (Raw&ₚ RawMDHMS RawSubSingleton)

equivalent : Equivalent UTCTimeFieldsRep UTCTimeFields
proj₁ equivalent (mk&ₚ year (mk&ₚ mdhms (─ refl) refl) eq) = mkUTCTime year mdhms eq
proj₂ equivalent (mkUTCTime year mdhms bs≡) = mk&ₚ year (mk&ₚ mdhms (─ refl) refl) bs≡

RawUTCTimeFields : Raw UTCTimeFields
RawUTCTimeFields = Iso.raw equivalent RawUTCTimeFieldsRep

RawUTCTime : Raw UTCTime
RawUTCTime = RawTLV _ RawUTCTimeFields
