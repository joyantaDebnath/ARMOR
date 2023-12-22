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
open import Data.Product.Relation.Binary.Lex.Strict
open import Data.Product.Relation.Binary.Pointwise.NonDependent
open import Relation.Binary.Core

module Armor.Data.X690-DER.Time.GeneralizedTime.TCB where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Seq.TCB     UInt8

-- https://datatracker.ietf.org/doc/html/rfc5280#section-4.1.2.5.2
--    The generalized time type, GeneralizedTime, is a standard ASN.1 type
--    for variable precision representation of time.  Optionally, the
--    GeneralizedTime field can include a representation of the time
--    differential between local and Greenwich Mean Time.

--    For the purposes of this profile, GeneralizedTime values MUST be
--    expressed in Greenwich Mean Time (Zulu) and MUST include seconds
--    (i.e., times are YYYYMMDDHHMMSSZ), even where the number of seconds
--    is zero.  GeneralizedTime values MUST NOT include fractional seconds.
   
record GeneralizedTimeFields (@0 bs : List UInt8) : Set where
  constructor mkGeneralizedTime
  field
    @0 {y m} : List UInt8
    year : Year₄ y
    mdhms : MDHMS m
    @0 bs≡ : bs ≡ y ++ m ++ [ # 'Z' ]

  getYear   = TimeType.getTime year
  getMonth  = MDHMS.getMonth mdhms
  getDay    = MDHMS.getDay mdhms
  getHour   = MDHMS.getHour mdhms
  getMinute = MDHMS.getMinute mdhms
  getSec    = MDHMS.getSec mdhms

GeneralizedTime : @0 List UInt8 → Set
GeneralizedTime = TLV Tag.GeneralizedTime GeneralizedTimeFields

GeneralizedTimeFieldsRep : @0 List UInt8 → Set
GeneralizedTimeFieldsRep = &ₚ (&ₚ Year₄ MDHMS) (λ x → Erased (x ≡ [ # 'Z' ]))

RawGeneralizedTimeFieldsRep : Raw GeneralizedTimeFieldsRep
RawGeneralizedTimeFieldsRep =
  Raw&ₚ (Raw&ₚ RawYear₄ RawMDHMS) RawSubSingleton

equivalent : Equivalent GeneralizedTimeFieldsRep GeneralizedTimeFields
proj₁ equivalent (mk&ₚ (mk&ₚ{bs₁ = y}{m} year mdhms refl) (─ refl) eq) =
  mkGeneralizedTime year mdhms (trans eq (++-assoc y m _))
proj₂ equivalent (mkGeneralizedTime{y}{m} year mdhms bs≡) =
  mk&ₚ (mk&ₚ year mdhms refl) (─ refl) (trans bs≡ (sym (++-assoc y m _)))

RawGeneralizedTimeFields : Raw GeneralizedTimeFields
RawGeneralizedTimeFields = Iso.raw equivalent RawGeneralizedTimeFieldsRep

RawGeneralizedTime : Raw GeneralizedTime
RawGeneralizedTime = RawTLV _ RawGeneralizedTimeFields


infix 4 _GeneralizedTimeFields<'_ _GeneralizedTimeFields<_ _GeneralizedTimeFields≤_

_GeneralizedTimeFields<'_ : Rel (Raw.D RawGeneralizedTimeFields) Level.0ℓ
_GeneralizedTimeFields<'_ = ×-Lex (Pointwise _≡_ _≡_) (×-Lex _≡_ _<_ _MDHMS<'_) (λ _ _ → ⊥)

_GeneralizedTimeFields<_
  : ∀ {@0 bs₁ bs₂} → (g₁ : GeneralizedTimeFields bs₁) (g₂ : GeneralizedTimeFields bs₂)
    → Set
g₁ GeneralizedTimeFields< g₂ =
  (Raw.to RawGeneralizedTimeFields g₁) GeneralizedTimeFields<' (Raw.to RawGeneralizedTimeFields g₂)

_GeneralizedTimeFields≤_ : {@0 bs₁ bs₂ : List UInt8} → (g₁ : GeneralizedTimeFields bs₁) (g₂ : GeneralizedTimeFields bs₂) → Set
g₁ GeneralizedTimeFields≤ g₂ = _≋_{A = GeneralizedTimeFields} g₁ g₂ ⊎ g₁ GeneralizedTimeFields< g₂
