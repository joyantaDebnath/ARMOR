open import Armor.Binary
open import Armor.Data.X509.PublicKey.Val.RSA.Ints.TCB
open import Armor.Data.X690-DER.Int
open import Armor.Data.X690-DER.TLV
import      Armor.Grammar.Definitions
import      Armor.Grammar.Seq
open import Armor.Prelude

module Armor.Data.X509.PublicKey.Val.RSA.Ints.Properties where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Seq         UInt8

iso : Iso RSAPkIntsFieldsRep RSAPkIntsFields
proj₁ iso = equivalent
proj₁ (proj₂ iso) (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = refl
proj₂ (proj₂ iso) (mkRSAPkIntsFields nval eval bs≡) = refl

@0 nosubstrings : NoSubstrings RSAPkIntsFields
nosubstrings =
  Iso.nosubstrings equivalent
    (Seq.nosubstrings TLV.nosubstrings TLV.nosubstrings)

@0 unambiguousFields : Unambiguous RSAPkIntsFields
unambiguousFields =
  Iso.unambiguous iso
    (Seq.unambiguous Int.unambiguous TLV.nosubstrings Int.unambiguous)

@0 unambiguous : Unambiguous RSAPkInts
unambiguous = TLV.unambiguous unambiguousFields

@0 nonmalleableFields : NonMalleable RawRSAPkIntsFields
nonmalleableFields =
  Iso.nonmalleable iso RawRSAPkIntsFieldsRep
    (Seq.nonmalleable Int.nonmalleable Int.nonmalleable)

@0 nonmalleable : NonMalleable RawRSAPkInts
nonmalleable = TLV.nonmalleable nonmalleableFields
