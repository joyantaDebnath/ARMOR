open import Armor.Binary
open import Armor.Data.X690-DER.Length.Properties as Length
open import Armor.Data.X690-DER.Length.TCB
open import Armor.Data.X690-DER.TLV.TCB
import      Armor.Data.X690-DER.Tag as Tag
open import Armor.Data.X690-DER.Time.GeneralizedTime.TCB as GeneralizedTime
  hiding (equivalent)
import      Armor.Data.X690-DER.Time.MDHMS.Properties as MDHMS
open import Armor.Data.X690-DER.Time.MDHMS.TCB
  hiding (equivalent)
open import Armor.Data.X690-DER.Time.TimeType.TCB
open import Armor.Data.X690-DER.Time.UTCTime.Properties  as UTCTime
open import Armor.Data.X690-DER.Time.UTCTime.TCB         as UTCTime
  hiding (equivalent)
open import Armor.Data.X690-DER.Time.Year.TCB
import      Armor.Grammar.Sum.TCB
import      Armor.Grammar.Definitions.Iso
import      Armor.Grammar.Definitions.NonMalleable.Base
open import Armor.Prelude
open import Data.Nat.Properties

module Armor.Data.X509.Validity.Time.TCB where

open Armor.Grammar.Definitions.Iso               UInt8
open Armor.Grammar.Definitions.NonMalleable.Base UInt8
open Armor.Grammar.Sum.TCB                       UInt8

-- https://datatracker.ietf.org/doc/html/rfc5280#section-4.1
-- Time ::= CHOICE {
--         utcTime        UTCTime,
--         generalTime    GeneralizedTime }

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

-- https://datatracker.ietf.org/doc/html/rfc5280#section-4.1.2.5.2
--    The generalized time type, GeneralizedTime, is a standard ASN.1 type
--    for variable precision representation of time.  Optionally, the
--    GeneralizedTime field can include a representation of the time
--    differential between local and Greenwich Mean Time.

--    For the purposes of this profile, GeneralizedTime values MUST be
--    expressed in Greenwich Mean Time (Zulu) and MUST include seconds
--    (i.e., times are YYYYMMDDHHMMSSZ), even where the number of seconds
--    is zero.  GeneralizedTime values MUST NOT include fractional seconds.
        
data Time (@0 bs : List UInt8) : Set where
  generalized : GeneralizedTime bs → Time bs
  utc         : UTCTime bs         → Time bs

TimeRep : @0 List UInt8 → Set
TimeRep = Sum GeneralizedTime UTCTime

equivalent : Equivalent TimeRep Time
proj₁ equivalent (Sum.inj₁ x) = generalized x
proj₁ equivalent (Sum.inj₂ x) = utc x
proj₂ equivalent (generalized x) = Sum.inj₁ x
proj₂ equivalent (utc x) = Sum.inj₂ x

RawTimeRep : Raw TimeRep
RawTimeRep = RawSum RawGeneralizedTime RawUTCTime

RawTime : Raw Time
RawTime = Iso.raw equivalent RawTimeRep

@0 windowByteString : ∀ {bs} → Year₂ bs → UInt8 × UInt8
windowByteString x = if ⌊ TimeType.getTime x ≥? 50 ⌋ then (# '1') , (# '9') else (# '2') , (# '0')

window : Window₂
window{bs} y = (─ windowByteString y) , help
  where
  open ≡-Reasoning

  bs≡ : Exists─ (UInt8 × UInt8) λ where (b₁ , b₂) → Erased (b₁ ∷ [ b₂ ] ≡ bs)
  proj₁ bs≡ = ─ ((lookup bs (subst₀ Fin (sym (TimeType.bsLen y)) (# 0))) , (lookup bs (subst₀ Fin (sym (TimeType.bsLen y)) (# 1))))
  proj₂ bs≡ = ─ (caseErased (singleton bs refl) ,′ (singleton (TimeType.bsLen y) refl) ret (const _) of λ where
    (singleton (x ∷ x₁ ∷ []) refl , singleton refl refl) → ─ refl)

  @0 b₁ b₂ : UInt8
  b₁ = proj₁ (¡ proj₁ bs≡)
  b₂ = proj₂ (¡ proj₁ bs≡)

  help : Year₄ (proj₁ (windowByteString y) ∷ [ proj₂ (windowByteString y) ] ++ bs)
  help with TimeType.getTime y ≥? 50
  ... | yes p =
    mkTimeType
      (fromWitness (((m≤m+n 48 1) , (m≤m+n 49 _ )) ∷ (((m≤m+n 48 _) , ≤-refl) ∷ (toWitness (TimeType.charset y)))))
      (singleton (1900 + TimeType.getTime y)
        (1900 + TimeType.getTime y ≡ asciiNum ((# '1') ∷ [ # '9' ] ++ bs) ∋ (begin
           1900 + TimeType.getTime y
         ≡⟨ cong₂ _+_
             (1 * 10 ^ 3 + 9 * 10 ^ 2 ≡ 1 * 10 ^ (1 + length bs) + 9 * 10 ^ length bs ∋
               cong (λ x → 1 * (10 ^ (1 + x)) + 9 * (10 ^ x)) {x = 2}{y = length bs}
                 (sym $ TimeType.bsLen y))
             (Singleton.x≡ (TimeType.time y)) ⟩
           1 * 10 ^ (1 + length bs) + 9 * 10 ^ length bs + asciiNum bs ≡⟨ +-assoc (1 * (10 ^ (1 + length bs))) (9 * 10 ^ length bs) _ ⟩
           asciiNum (# '1' ∷ [ # '9' ] ++ bs) ∎)))
      (cong (2 +_) (TimeType.bsLen y))
      (z≤n , (+-monoʳ-≤ 1900 (≤-trans (proj₂ (TimeType.range y)) (toWitness{Q = 99 ≤? 8099} tt))))
  ... | no ¬p =
    mkTimeType
      (fromWitness (((m≤m+n 48 _) , (m≤m+n 50 _)) ∷ (((m≤m+n 48 _) , (m≤n+m _ 9)) ∷ (toWitness (TimeType.charset y)))))
      (singleton (2000 + TimeType.getTime y)
        (2000 + TimeType.getTime y ≡ asciiNum (# '2' ∷ [ # '0' ] ++ bs) ∋
          2000 + TimeType.getTime y
            ≡⟨ cong₂ _+_{x = 2 * 10 ^ 3}{y = 2 * 10 ^ (1 + length bs)}
                 (cong (λ x → 2 * (10 ^ (1 + x))) {x = 2} {y = length bs}
                   (sym $ TimeType.bsLen y))
                 (Singleton.x≡ (TimeType.time y)) ⟩
          2 * 10 ^ (1 + length bs) + asciiNum bs ∎ ))
      (cong (2 +_) (TimeType.bsLen y))
      (z≤n , (+-monoʳ-≤ 2000 (≤-trans (proj₂ (TimeType.range y)) (toWitness{Q = 99 ≤? 7999} tt))))

@0 toGeneralizedTimeByteString : ∀ {bs} → Time bs → List UInt8
toGeneralizedTimeByteString{bs} (generalized x) = bs
toGeneralizedTimeByteString {bs} (utc (mkTLV{v = v} len val len≡ refl)) =
    Tag.GeneralizedTime ∷ # 15
  ∷ (proj₁ (windowByteString (UTCTimeFields.year val))
  ∷ [ proj₂ (windowByteString (UTCTimeFields.year val)) ])
  ++ v

toGeneralizedTime : ∀ {@0 bs} → (t : Time bs) → GeneralizedTime (toGeneralizedTimeByteString t)
toGeneralizedTime (generalized x) = x
toGeneralizedTime (utc (mkTLV len (mkUTCTime{y}{m} year mdhms refl) len≡ refl)) =
  mkTLV
    (short (mkShort (# 15) (toWitness{Q = _ ≤? _} tt) refl))
    (mkGeneralizedTime (proj₂ (window year)) mdhms refl)
    (cong (2 +_) (sym $ begin
      length (y ++ m ++ [ # 'Z' ]) ≡⟨ length-++ y ⟩
      length y + length (m ++ [ # 'Z' ])
        ≡⟨ cong₂ _+_ (TimeType.bsLen year)
             (begin
               length (m ++ [ # 'Z' ]) ≡⟨ length-++ m ⟩
               length m + 1 ≡⟨ cong (_+ 1) (MDHMS.length≡ mdhms) ⟩
               11 ∎) ⟩
      13 ∎))
    refl
  where
  open ≡-Reasoning

getYear getMonth getDay getHour getMinute getSec : ∀ {@0 bs} → Time bs → ℕ

getYear time  = GeneralizedTimeFields.getYear (TLV.val (toGeneralizedTime time))

getMonth (generalized x) = GeneralizedTimeFields.getMonth (TLV.val x)
getMonth (utc x) = UTCTimeFields.getMonth (TLV.val x)

getDay (generalized x) = GeneralizedTimeFields.getDay (TLV.val x)
getDay (utc x) = UTCTimeFields.getDay (TLV.val x)

getHour (generalized x) = GeneralizedTimeFields.getHour (TLV.val x)
getHour (utc x) = UTCTimeFields.getHour (TLV.val x)

getMinute (generalized x) = GeneralizedTimeFields.getMinute (TLV.val x)
getMinute (utc x) = UTCTimeFields.getMinute (TLV.val x)

getSec (generalized x) = GeneralizedTimeFields.getSec (TLV.val x)
getSec (utc x) = UTCTimeFields.getSec (TLV.val x)
