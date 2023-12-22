open import Armor.Binary
open import Armor.Data.X690-DER.TLV
open import Armor.Data.X690-DER.Time.UTCTime.TCB
open import Armor.Data.X690-DER.Time.MDHMS
open import Armor.Data.X690-DER.Time.TimeType
open import Armor.Data.X690-DER.Time.Year
import      Armor.Grammar.Definitions
import      Armor.Grammar.Seq
open import Armor.Prelude

module Armor.Data.X690-DER.Time.UTCTime.Properties where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Seq         UInt8

@0 length≡ : ∀ {@0 bs} → UTCTimeFields bs → length bs ≡ 13
length≡ (mkUTCTime{y}{m} year mdhms refl) = begin
  length (y ++ m ++ [ # 'Z' ]) ≡⟨ length-++ y ⟩
  length y + length (m ++ [ # 'Z' ])
    ≡⟨ cong₂ _+_
         (TimeType.bsLen year)
         (begin
           length (m ++ [ # 'Z' ]) ≡⟨ length-++ m ⟩
           length m + 1 ≡⟨ cong (_+ 1) (MDHMS.length≡ mdhms) ⟩
           11 ∎) ⟩
  13 ∎
  where
  open ≡-Reasoning

@0 nosubstrings : NoSubstrings UTCTimeFields
nosubstrings =
  Iso.nosubstrings equivalent
    (Seq.nosubstrings TimeType.nosubstrings
    (Seq.nosubstrings MDHMS.nosubstrings (λ where _ (─ refl) (─ refl) → refl)))

iso : Iso UTCTimeFieldsRep UTCTimeFields
proj₁ iso = equivalent
proj₁ (proj₂ iso) (mk&ₚ year (mk&ₚ mdhms (─ refl) refl) bs≡) = refl
proj₂ (proj₂ iso) (mkUTCTime year mdhms bs≡) = refl

@0 unambiguousFields : Unambiguous UTCTimeFields
unambiguousFields =
  Iso.unambiguous iso
    (Seq.unambiguous TimeType.unambiguous TimeType.nosubstrings
    (Seq.unambiguous MDHMS.unambiguous MDHMS.nosubstrings
    (erased-unique ≡-unique)))

@0 unambiguous : Unambiguous UTCTime
unambiguous = TLV.unambiguous unambiguousFields

@0 nonmalleableFields : NonMalleable RawUTCTimeFields
nonmalleableFields =
  Iso.nonmalleable iso RawUTCTimeFieldsRep nm
  where
  nm : NonMalleable RawUTCTimeFieldsRep
  nm =  Seq.nonmalleable TimeType.nonmalleable
       (Seq.nonmalleable MDHMS.nonmalleable
                         (subsingleton⇒nonmalleable (λ where (─ _ , ─ refl) (─ _ , ─ refl) → refl)))

@0 nonmalleable : NonMalleable RawUTCTime
nonmalleable = TLV.nonmalleable nonmalleableFields

instance
  eq : Eq (Exists─ (List UInt8) UTCTimeFields)
  eq = Iso.isoEq iso (Seq.eq&ₚ it (Seq.eq&ₚ it (record { _≟_ = λ where (─ _ , ─ refl) (─ _ , ─ refl) → yes refl })))
