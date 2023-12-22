open import Armor.Binary
open import Armor.Data.X509.PublicKey.Alg.ECPKParameters.ECParameters.Curve.TCB
open import Armor.Data.X690-DER.BitString
open import Armor.Data.X690-DER.OctetString
open import Armor.Data.X690-DER.TLV
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Definitions
import      Armor.Grammar.Option
import      Armor.Grammar.Properties
import      Armor.Grammar.Seq
open import Armor.Prelude

module Armor.Data.X509.PublicKey.Alg.ECPKParameters.ECParameters.Curve.Properties where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Option      UInt8
open Armor.Grammar.Properties  UInt8
open Armor.Grammar.Seq         UInt8
open ≡-Reasoning

iso : Iso CurveFieldsRep CurveFields
proj₁ iso = equivalent
proj₁ (proj₂ iso) (mk&ₚ{bs₂ = bs₃} (mk&ₚ{bs₁ = bs₁}{bs₂} a b refl) seed refl) = ‼
  ≡-elimₖ
    (λ e → mk&ₚ (mk&ₚ a b refl) seed e ≡  mk&ₚ (mk&ₚ a b refl) seed refl)
    refl
    (trans (++-assoc bs₁ bs₂ bs₃) (sym ((++-assoc bs₁ bs₂ bs₃))))
proj₂ (proj₂ iso) (mkCurveFields a b seed refl) = ‼
  ≡-elimₖ
    (λ e → mkCurveFields a b seed e ≡ mkCurveFields a b seed refl)
    refl _

@0 unambiguousFields : Unambiguous CurveFields
unambiguousFields = Iso.unambiguous iso
  (Seq.unambiguous (Seq.unambiguous OctetString.unambiguous TLV.nosubstrings OctetString.unambiguous)
    (Seq.nosubstrings TLV.nosubstrings TLV.nosubstrings)
      (Option.unambiguous BitString.unambiguous TLV.nonempty))

@0 unambiguous : Unambiguous Curve
unambiguous = TLV.unambiguous unambiguousFields

@0 nonmalleableFields : NonMalleable RawCurveFields
nonmalleableFields =
  Iso.nonmalleable iso RawCurveFieldsRep
    (Seq.nonmalleable (Seq.nonmalleable OctetString.nonmalleable OctetString.nonmalleable)
      (Option.nonmalleable _ BitString.nonmalleable))

@0 nonmalleable : NonMalleable RawCurve
nonmalleable = TLV.nonmalleable nonmalleableFields
