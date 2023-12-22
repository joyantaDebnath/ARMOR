open import Armor.Binary
open import Armor.Data.X509.Extension
import      Armor.Data.X509.Extension.TCB.OIDs as OIDs
open import Armor.Data.X509.PublicKey
open import Armor.Data.X509.Name
open import Armor.Data.X509.Name.TCB as Name
open import Armor.Data.X509.SignAlg
open import Armor.Data.X509.SignAlg.TCB
open import Armor.Data.X509.TBSCert.TCB
open import Armor.Data.X509.TBSCert.UID.TCB
open import Armor.Data.X509.TBSCert.Version
open import Armor.Data.X509.Validity
open import Armor.Data.X690-DER.BitString
open import Armor.Data.X690-DER.Default
open import Armor.Data.X690-DER.Int
open import Armor.Data.X690-DER.OctetString
open import Armor.Data.X690-DER.Sequence
open import Armor.Data.X690-DER.TLV
import      Armor.Grammar.Definitions
import      Armor.Grammar.Option
import      Armor.Grammar.Parallel  
-- import      Armor.Grammar.Properties
import      Armor.Grammar.Seq
open import Armor.Data.X690-DER.Tag as Tag
open import Armor.Prelude
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Armor.Data.X509.TBSCert.Properties where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Option      UInt8
open Armor.Grammar.Parallel    UInt8
-- open Armor.Grammar.Properties  UInt8
open Armor.Grammar.Seq         UInt8

iso : Iso TBSCertFieldsRep TBSCertFields
proj₁ iso = equivalentTBSCertFields
proj₁ (proj₂ iso) (mk&ₚ (mk&ₚ{bs₁ = bs₁}{bs₂} fstₚ₁ sndₚ₁ refl) (mk&ₚ{bs₁ = bs₃} fstₚ₂ (mk&ₚ{bs₁ = bs₄} fstₚ₃ (mk&ₚ{bs₁ = bs₅} fstₚ₄ (mk&ₚ{bs₁ = bs₆} fstₚ₅ (mk&ₚ{bs₁ = bs₇} (mk×ₚ fstₚ₆ s) (mk&ₚ{bs₁ = bs₈} fstₚ₇ (mk&ₚ{bs₁ = bs₉}{bs₁₀} fstₚ₈ sndₚ₂ refl) refl) refl) refl) refl) refl) refl) bs≡) =
  subst₀ (λ eq → mk&ₚ _ _ eq ≡ mk&ₚ _ _ bs≡) (≡-unique bs≡ (trans₀ (trans₀ bs≡ _) _)) refl
proj₂ (proj₂ iso) (mkTBSCertFields version serial signAlg issuer validity subject pk pkBytes issuerUID subjectUID extensions bs≡) =
  subst₀ (λ eq → mkTBSCertFields version serial signAlg issuer validity subject pk pkBytes issuerUID subjectUID extensions eq ≡ mkTBSCertFields _ _ _ _ _ _ _ _ _ _ _ bs≡) (≡-unique bs≡ _) refl

@0 unambiguous : Unambiguous TBSCert
unambiguous = TLV.unambiguous (Iso.unambiguous iso ua₈)
  where
  ua₂ : Unambiguous Rep₂
  ua₂ =
    Seq.unambiguous₂Option₃
      (TLV.unambiguous BitString.unambiguousValue) TLV.nosubstrings TLV.nonempty
      (TLV.unambiguous BitString.unambiguousValue) TLV.nosubstrings TLV.nonempty
      Extension.unambiguous TLV.nonempty
      (TLV.noconfusion λ ()) (TLV.noconfusion λ ()) (TLV.noconfusion λ ())

  ua₃ : Unambiguous Rep₃
  ua₃ = Seq.unambiguous
          (Parallel.unambiguous×ₚ PublicKey.unambiguous OctetString.unambiguousValue)
          (Parallel.nosubstrings₁ TLV.nosubstrings) ua₂

  ua₄ : Unambiguous Rep₄
  ua₄ = Seq.unambiguous Name.unambiguous TLV.nosubstrings ua₃

  ua₅ : Unambiguous Rep₅
  ua₅ = Seq.unambiguous Validity.unambiguous TLV.nosubstrings ua₄

  ua₆ : Unambiguous Rep₆
  ua₆ = Seq.unambiguous Name.unambiguous TLV.nosubstrings ua₅

  ua₇ : Unambiguous Rep₇
  ua₇ = Seq.unambiguous SignAlg.unambiguous SignAlg.nosubstrings ua₆

  ua₈ : Unambiguous TBSCertFieldsRep
  ua₈ = Seq.unambiguous
          (Sequence.unambiguousDefault₁ v1[0]ExplicitVersion
            Version.unambiguous[0]Explicit
            TLV.nosubstrings
            Int.unambiguous
            (TLV.noconfusion λ ()))
          (Sequence.nosubstringsDefault₁ v1[0]ExplicitVersion TLV.nosubstrings TLV.nosubstrings (TLV.noconfusion λ ()))
          ua₇

@0 nonmalleable : NonMalleable RawTBSCert
nonmalleable = TLV.nonmalleable(Iso.nonmalleable iso RawTBSCertFieldsRep nm)
  where 
  RawRep =  Raw&ₚ (RawOption (RawTLV Tag.A82 RawBitStringValue))
                             (RawOption RawExtensions)
  RawRep₁ = Raw&ₚ (RawOption (RawTLV Tag.A81 RawBitStringValue)) RawRep
  RawRep₂ = Raw&ₚ (Raw×ₚ RawPublicKey RawOctetStringValue) RawRep₁
  RawRep₃ = Raw&ₚ Name.RawName RawRep₂
  RawRep₄ = Raw&ₚ Validity.RawValidity RawRep₃
  RawRep₅ = Raw&ₚ Name.RawName RawRep₄
  RawRep₆ = Raw&ₚ RawSignAlg RawRep₅
  RawRep₇ = Raw&ₚ (Raw&ₚ (RawDefault Raw[0]ExplicitVersion v1[0]ExplicitVersion) RawInt) RawRep₆

  nm : NonMalleable RawTBSCertFieldsRep
  nm =  Seq.nonmalleable
          {ra = Raw&ₚ (RawDefault Raw[0]ExplicitVersion v1[0]ExplicitVersion) RawInt}
          {rb = RawRep₆}
          (Seq.nonmalleable (Default.nonmalleable v1[0]ExplicitVersion Version.nonmalleable[0]Explicit) Int.nonmalleable)
       (Seq.nonmalleable{ra = RawSignAlg}{rb = RawRep₅}
         SignAlg.nonmalleable
       (Seq.nonmalleable{ra = Name.RawName}{rb = RawRep₄}
         Name.nonmalleable
       (Seq.nonmalleable{ra = Validity.RawValidity}{rb = RawRep₃}
         Validity.nonmalleable
       (Seq.nonmalleable{ra = RawName}{rb = RawRep₂}
         Name.nonmalleable
       (Seq.nonmalleable{rb = RawRep₁}
         (Parallel.nonmalleable×ₚ PublicKey.nonmalleable OctetString.nonmalleableValue)
       (Seq.nonmalleable{rb = RawRep}
         (Option.nonmalleable _ (TLV.nonmalleable BitString.nonmalleableValue))
       (Seq.nonmalleable{rb = RawOption RawExtensions}
         (Option.nonmalleable _ (TLV.nonmalleable BitString.nonmalleableValue))
         (Option.nonmalleable _ Extension.nonmalleable))))))))
