open import Armor.Binary
open import Armor.Data.X509.PublicKey.Alg.ECPKParameters.ECParameters.FieldID.CharTwo.Basis
open import Armor.Data.X509.PublicKey.Alg.ECPKParameters.ECParameters.FieldID.CharTwo.TCB
open import Armor.Data.X690-DER.Int
open import Armor.Data.X690-DER.TLV
import      Armor.Grammar.Definitions
import      Armor.Grammar.Seq
open import Armor.Prelude

module Armor.Data.X509.PublicKey.Alg.ECPKParameters.ECParameters.FieldID.CharTwo.Properties where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Seq         UInt8

iso : Iso CharTwoFieldsRep CharTwoFields
proj₁ iso = equivalent
proj₁ (proj₂ iso) (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = refl
proj₂ (proj₂ iso) (mkCharTwoFields m basis bs≡) = refl

@0 nosubstrings : NoSubstrings CharTwoFields
nosubstrings =
  Iso.nosubstrings equivalent
    (Seq.nosubstrings TLV.nosubstrings Basis.nosubstrings)

@0 unambiguous : Unambiguous CharTwo
unambiguous =
  TLV.unambiguous
    (Iso.unambiguous iso
      (Seq.unambiguous Int.unambiguous TLV.nosubstrings Basis.unambiguous))

@0 nonmalleable : NonMalleable RawCharTwo
nonmalleable =
  TLV.nonmalleable{R = RawCharTwoFields}
    (Iso.nonmalleable iso RawCharTwoFieldsRep
      (Seq.nonmalleable{ra = RawInt}{rb = RawBasisFields} Int.nonmalleable Basis.nonmalleable))

instance
  eq≋ : Eq≋ CharTwoFields
  eq≋ =
    Iso.isoEq≋ iso
      (Seq.eq≋&ₚ it it)
