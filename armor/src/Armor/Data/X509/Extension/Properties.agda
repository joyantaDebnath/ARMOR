open import Armor.Binary
open import Armor.Data.X509.Extension.AIA
open import Armor.Data.X509.Extension.AKI
open import Armor.Data.X509.Extension.BC
open import Armor.Data.X509.Extension.CRLDistPoint
open import Armor.Data.X509.Extension.CertPolicy
open import Armor.Data.X509.Extension.EKU
open import Armor.Data.X509.Extension.IAN
open import Armor.Data.X509.Extension.INAP
open import Armor.Data.X509.Extension.KU
open import Armor.Data.X509.Extension.NC
open import Armor.Data.X509.Extension.PC
open import Armor.Data.X509.Extension.PM
open import Armor.Data.X509.Extension.SAN
open import Armor.Data.X509.Extension.SKI
import      Armor.Data.X509.Extension.TCB.OIDs as OIDs
open import Armor.Data.X509.Extension.TCB
open import Armor.Data.X509.GeneralNames
open import Armor.Data.X690-DER.BitString
open import Armor.Data.X690-DER.Boool
open import Armor.Data.X690-DER.Default
open import Armor.Data.X690-DER.Int
open import Armor.Data.X690-DER.OID
open import Armor.Data.X690-DER.OctetString
open import Armor.Data.X690-DER.Sequence
open import Armor.Data.X690-DER.SequenceOf
open import Armor.Data.X690-DER.TLV
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Definitions
import      Armor.Grammar.Option
import      Armor.Grammar.Parallel
import      Armor.Grammar.Properties
import      Armor.Grammar.Seq
import      Armor.Grammar.Sum
open import Armor.Prelude
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Armor.Data.X509.Extension.Properties where

open ≡-Reasoning

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Option      UInt8
open Armor.Grammar.Parallel    UInt8
open Armor.Grammar.Properties  UInt8
open Armor.Grammar.Seq         UInt8
open Armor.Grammar.Sum         UInt8

module Fields where
  iso : ∀ {@0 P} {A : @0 List UInt8 → Set}
        → Iso (ExtensionFieldsRep P A) (ExtensionFields P A)
  proj₁ iso = equivalentExtensionFields
  proj₁ (proj₂ iso) (mk&ₚ (mk×ₚ fstₚ₁ (─ sndₚ₁)) (mk&ₚ fstₚ₂ sndₚ₂ refl) refl) = refl
  proj₂ (proj₂ iso) (mkExtensionFields extnId extnId≡ crit extension refl) = refl

  @0 unambiguous : ∀ {@0 P} {A : @0 List UInt8 → Set} → (∀ {x} → Unique (P x)) → Unambiguous A → NoConfusion Boool A → Unambiguous (ExtensionFields P A)
  unambiguous{P}{A} uaₚ ua₁ nc =
    Iso.unambiguous iso
      (Seq.unambiguous{A = Σₚ OID λ _ x → Erased (P (TLV.v x))}{B = &ₚ (Default Boool falseBoool) A}
        (Parallel.unambiguous OID.unambiguous λ a → erased-unique uaₚ )
        (Parallel.nosubstrings₁ TLV.nosubstrings)
        (Sequence.unambiguousDefault₁ _ Boool.unambiguous TLV.nosubstrings ua₁ nc))

  @0 nonmalleable : ∀ {@0 P : List UInt8 → Set}{A : @0 List UInt8 → Set} {ra : Raw A} → (∀ {x} → Unique (P x)) → NonMalleable ra → NonMalleable (RawExtensionFields{P} ra)
  nonmalleable{ra = ra} x x₁ =
    Iso.nonmalleable iso (RawExtensionFieldsRep ra)
    (Seq.nonmalleable
     (Parallel.nonmalleable₁ RawOID OID.nonmalleable λ a p₁ p₂ → erased-unique x p₁ p₂)
     (Seq.nonmalleable
       (Default.nonmalleable _ Boool.nonmalleable) x₁))

module Select where
  iso : Iso SelectExtnRep SelectExtn
  proj₁ iso = equivalent
  proj₁ (proj₂ iso) (Sum.inj₁ x) = refl
  proj₁ (proj₂ iso) (Sum.inj₂ (Sum.inj₁ x)) = refl
  proj₁ (proj₂ iso) (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x))) = refl
  proj₁ (proj₂ iso) (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x)))) = refl
  proj₁ (proj₂ iso) (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x)))))                                                        = refl
  proj₁ (proj₂ iso) (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x))))))                                             = refl
  proj₁ (proj₂ iso) (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x)))))))                                  = refl
  proj₁ (proj₂ iso) (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x))))))))                       = refl
  proj₁ (proj₂ iso) (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x)))))))))            = refl
  proj₁ (proj₂ iso) (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x)))))))))) = refl
  proj₁ (proj₂ iso) (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x))))))))))) = refl
  proj₁ (proj₂ iso) (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x)))))))))))) = refl
  proj₁ (proj₂ iso) (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x))))))))))))) = refl
  proj₁ (proj₂ iso) (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x)))))))))))))) = refl
  proj₁ (proj₂ iso) (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ x)))))))))))))) = refl
  proj₂ (proj₂ iso) (akiextn x) = refl
  proj₂ (proj₂ iso) (skiextn x) = refl
  proj₂ (proj₂ iso) (kuextn x)  = refl
  proj₂ (proj₂ iso) (ekuextn x) = refl
  proj₂ (proj₂ iso) (bcextn x)  = refl
  proj₂ (proj₂ iso) (ianextn x) = refl
  proj₂ (proj₂ iso) (sanextn x) = refl
  proj₂ (proj₂ iso) (cpextn x)  = refl
  proj₂ (proj₂ iso) (crlextn x) = refl
  proj₂ (proj₂ iso) (ncextn x) = refl
  proj₂ (proj₂ iso) (pcextn x) = refl
  proj₂ (proj₂ iso) (pmextn x) = refl
  proj₂ (proj₂ iso) (inapextn x) = refl
  proj₂ (proj₂ iso) (aiaextn x) = refl
  proj₂ (proj₂ iso) (other x)   = refl

  @0 unambiguous : Unambiguous SelectExtn
  unambiguous =
    Iso.unambiguous iso
      (Sum.unambiguous
        (Fields.unambiguous ≡-unique AKI.unambiguous (TLV.noconfusion λ ()))
        (Sum.unambiguous
          (Fields.unambiguous ≡-unique SKI.unambiguous (TLV.noconfusion λ ()))
          (Sum.unambiguous
            (Fields.unambiguous ≡-unique KU.unambiguous (TLV.noconfusion λ ()))
            (Sum.unambiguous
              (Fields.unambiguous ≡-unique EKU.unambiguous (TLV.noconfusion λ ()))
              (Sum.unambiguous
                (Fields.unambiguous ≡-unique BC.unambiguous (TLV.noconfusion λ ()))
                (Sum.unambiguous
                  (Fields.unambiguous ≡-unique IAN.unambiguous (TLV.noconfusion λ ()))
                  (Sum.unambiguous
                    (Fields.unambiguous ≡-unique SAN.unambiguous (TLV.noconfusion λ ()))
                    (Sum.unambiguous
                       (Fields.unambiguous ≡-unique CertPolicy.unambiguous  (TLV.noconfusion λ ()))
                      (Sum.unambiguous
                        (Fields.unambiguous ≡-unique CRLDistPoint.unambiguous (TLV.noconfusion λ ()))
                        (Sum.unambiguous
                          (Fields.unambiguous ≡-unique NC.unambiguous (TLV.noconfusion λ ()))
                          (Sum.unambiguous
                            (Fields.unambiguous ≡-unique PC.unambiguous (TLV.noconfusion λ ()))
                            (Sum.unambiguous
                              (Fields.unambiguous ≡-unique PM.unambiguous (TLV.noconfusion λ ()))
                              (Sum.unambiguous
                                (Fields.unambiguous ≡-unique INAP.unambiguous (TLV.noconfusion λ ()))
                                (Sum.unambiguous
                                  (Fields.unambiguous ≡-unique AIA.unambiguous (TLV.noconfusion λ ()))
                                (Fields.unambiguous ua
                                  OctetString.unambiguous (TLV.noconfusion λ ()))
                              noconfusion₀)
                            noconfusion₁₃)
                          noconfusion₁₂)
                        noconfusion₁₁)
                      noconfusion₁₀)
                    noconfusion₉)
                  noconfusion₈)
                noconfusion₇)
              noconfusion₆)
            noconfusion₅)
          noconfusion₄)
        noconfusion₃)
      noconfusion₂)
    noconfusion₁)
    where
    noconfusionOIDS : ∀ {@0 A B oid₁ oid₂} → oid₁ ≢ oid₂ → NoConfusion (ExtensionFields (_≡ oid₁) A) (ExtensionFields (_≡ oid₂) B)
    noconfusionOIDS oid≢ {xs₁}{ys₁}{xs₂}{ys₂}++≡ (mkExtensionFields{oex = oex}{cex}{ocex} extnId extnId≡ crit extension bs≡) (mkExtensionFields{oex = oex₁}{cex₁}{ocex₁} extnId₁ extnId≡₁ crit₁ extension₁ bs≡₁) =
      contradiction oid≡ λ where refl → oid≢ (trans₀ (sym extnId≡) (trans v≡ extnId≡₁) {- extnId≡₁ -})
      where
      @0 bs≡' : oex ++ cex ++ ocex ++ ys₁ ≡ oex₁ ++ cex₁ ++ ocex₁ ++ ys₂
      bs≡' = begin oex ++ cex ++ ocex ++ ys₁ ≡⟨ solve (++-monoid UInt8) ⟩
                   (oex ++ cex ++ ocex) ++ ys₁ ≡⟨ cong (_++ ys₁) (sym bs≡) ⟩
                   xs₁ ++ ys₁ ≡⟨ ++≡ ⟩
                   xs₂ ++ ys₂ ≡⟨ cong (_++ ys₂) bs≡₁ ⟩
                   (oex₁ ++ cex₁ ++ ocex₁) ++ ys₂ ≡⟨ solve (++-monoid UInt8) ⟩
                   oex₁ ++ cex₁ ++ ocex₁ ++ ys₂ ∎

      @0 oid≡ : oex ≡ oex₁
      oid≡ = TLV.nosubstrings bs≡' extnId extnId₁

      @0 oidT≡ : _≋_{A = OID} extnId extnId₁
      oidT≡ = mk≋ oid≡ (OID.unambiguous _ _)

      @0 v≡ : TLV.v extnId ≡ TLV.v extnId₁
      v≡ = caseErased oidT≡ ret (const _) of λ where
        ≋-refl → ─ refl

    noconfusionOIDN : ∀ {@0 A B oid} → (oid ∈ supportedExtensions) → NoConfusion (ExtensionFields (_≡ oid) A) (ExtensionFields (False ∘ (_∈? supportedExtensions)) B)
    noconfusionOIDN{oid = oid} supported {xs₁} {ys₁} {xs₂} {ys₂} ++≡ (mkExtensionFields {oex = oex} {cex} {ocex} extnId refl crit extension bs≡) (mkExtensionFields {oex = oex₁} {cex₁} {ocex₁} extnId₁ extnId≡₁ crit₁ extension₁ bs≡₁) =
      contradiction (subst (_∈ supportedExtensions) v≡ supported) (toWitnessFalse extnId≡₁) {- (toWitnessFalse extnId≡₁ )-}
      where
      @0 bs≡' : oex ++ cex ++ ocex ++ ys₁ ≡ oex₁ ++ cex₁ ++ ocex₁ ++ ys₂
      bs≡' = begin oex ++ cex ++ ocex ++ ys₁ ≡⟨ solve (++-monoid UInt8) ⟩
                   (oex ++ cex ++ ocex) ++ ys₁ ≡⟨ cong (_++ ys₁) (sym bs≡) {- (sym bs≡) -} ⟩
                   xs₁ ++ ys₁ ≡⟨ ++≡ ⟩
                   xs₂ ++ ys₂ ≡⟨ cong (_++ ys₂) bs≡₁ ⟩
                   (oex₁ ++ cex₁ ++ ocex₁) ++ ys₂ ≡⟨ solve (++-monoid UInt8) ⟩
                   oex₁ ++ cex₁ ++ ocex₁ ++ ys₂ ∎

      @0 oid≡ : oex ≡ oex₁
      oid≡ = TLV.nosubstrings bs≡' extnId extnId₁

      @0 oidT≡ : _≋_{A = OID} extnId extnId₁
      oidT≡ = mk≋ oid≡ (OID.unambiguous _ _)

      @0 v≡ : TLV.v extnId ≡ TLV.v extnId₁
      v≡ = caseErased oidT≡ ret (const _) of λ where
        ≋-refl → ─ refl

    noconfusion₁ : NoConfusion (ExtensionFields (_≡ OIDs.AKILit) AKIFields) (Sum _ _)
    noconfusion₁ =
      Sum.noconfusion{ExtensionFields (_≡ OIDs.AKILit) AKIFields}
        (noconfusionOIDS λ ())
        (Sum.noconfusion{ExtensionFields (_≡ OIDs.AKILit) AKIFields}
          (noconfusionOIDS λ ())
          (Sum.noconfusion{ExtensionFields (_≡ OIDs.AKILit) AKIFields}
            (noconfusionOIDS λ ())
            (Sum.noconfusion{ExtensionFields (_≡ OIDs.AKILit) AKIFields}
              (noconfusionOIDS λ ())
              (Sum.noconfusion{ExtensionFields (_≡ OIDs.AKILit) AKIFields}
                (noconfusionOIDS λ ())
                (Sum.noconfusion{ExtensionFields (_≡ OIDs.AKILit) AKIFields}
                  (noconfusionOIDS λ ())
                  (Sum.noconfusion{ExtensionFields (_≡ OIDs.AKILit) AKIFields}
                    (noconfusionOIDS λ ())
                    (Sum.noconfusion{ExtensionFields (_≡ OIDs.AKILit) AKIFields}
                      (noconfusionOIDS λ ())
                      (Sum.noconfusion{ExtensionFields (_≡ OIDs.AKILit) AKIFields}
                        (noconfusionOIDS λ ())
                        (Sum.noconfusion{ExtensionFields (_≡ OIDs.AKILit) AKIFields}
                          (noconfusionOIDS λ ())
                          (Sum.noconfusion{ExtensionFields (_≡ OIDs.AKILit) AKIFields}
                            (noconfusionOIDS λ ())
                            (Sum.noconfusion{ExtensionFields (_≡ OIDs.AKILit) AKIFields}
                              (noconfusionOIDS λ ())
                              (Sum.noconfusion{ExtensionFields (_≡ OIDs.AKILit) AKIFields}
                                (noconfusionOIDS λ ()) (noconfusionOIDN (toWitness{Q = _ ∈? _} tt))))))))))))))

    noconfusion₂ : NoConfusion (ExtensionFields (_≡ OIDs.SKILit) SKIFields) (Sum _ _)
    noconfusion₂ =
      Sum.noconfusion{ExtensionFields (_≡ OIDs.SKILit) SKIFields}
        (noconfusionOIDS λ ())
        (Sum.noconfusion{ExtensionFields (_≡ OIDs.SKILit) SKIFields}
          (noconfusionOIDS λ ())
          (Sum.noconfusion{ExtensionFields (_≡ OIDs.SKILit) SKIFields}
            (noconfusionOIDS λ ())
            (Sum.noconfusion{ExtensionFields (_≡ OIDs.SKILit) SKIFields}
              (noconfusionOIDS λ ())
              (Sum.noconfusion{ExtensionFields (_≡ OIDs.SKILit) SKIFields}
                (noconfusionOIDS λ ())
                (Sum.noconfusion{ExtensionFields (_≡ OIDs.SKILit) SKIFields}
                  (noconfusionOIDS λ ())
                  (Sum.noconfusion{ExtensionFields (_≡ OIDs.SKILit) SKIFields}
                    (noconfusionOIDS λ ())
                    (Sum.noconfusion{ExtensionFields (_≡ OIDs.SKILit) SKIFields}
                      (noconfusionOIDS λ ())
                      (Sum.noconfusion{ExtensionFields (_≡ OIDs.SKILit) SKIFields}
                        (noconfusionOIDS λ ())
                        (Sum.noconfusion{ExtensionFields (_≡ OIDs.SKILit) SKIFields}
                          (noconfusionOIDS λ ())
                          (Sum.noconfusion{ExtensionFields (_≡ OIDs.SKILit) SKIFields}
                            (noconfusionOIDS λ ())
                            (Sum.noconfusion{ExtensionFields (_≡ OIDs.SKILit) SKIFields}
                              (noconfusionOIDS λ ()) (noconfusionOIDN (toWitness{Q = _ ∈? _} tt)))))))))))))


    noconfusion₃ : NoConfusion (ExtensionFields (_≡ OIDs.KULit)  KUFields)  (Sum _ _)
    noconfusion₃ =
      Sum.noconfusion{ExtensionFields (_≡ OIDs.KULit) KUFields}
        (noconfusionOIDS λ ())
        (Sum.noconfusion{ExtensionFields (_≡ OIDs.KULit) KUFields}
          (noconfusionOIDS λ ())
          (Sum.noconfusion{ExtensionFields (_≡ OIDs.KULit) KUFields}
            (noconfusionOIDS λ ())
            (Sum.noconfusion{ExtensionFields (_≡ OIDs.KULit) KUFields}
              (noconfusionOIDS λ ())
              (Sum.noconfusion{ExtensionFields (_≡ OIDs.KULit) KUFields}
                (noconfusionOIDS λ ())
                (Sum.noconfusion{ExtensionFields (_≡ OIDs.KULit) KUFields}
                  (noconfusionOIDS λ ())
                  (Sum.noconfusion{ExtensionFields (_≡ OIDs.KULit) KUFields}
                    (noconfusionOIDS λ ())
                    (Sum.noconfusion{ExtensionFields (_≡ OIDs.KULit) KUFields}
                      (noconfusionOIDS λ ())
                      (Sum.noconfusion{ExtensionFields (_≡ OIDs.KULit) KUFields}
                        (noconfusionOIDS λ ())
                        (Sum.noconfusion{ExtensionFields (_≡ OIDs.KULit) KUFields}
                          (noconfusionOIDS λ ())
                          (Sum.noconfusion{ExtensionFields (_≡ OIDs.KULit) KUFields}
                            (noconfusionOIDS λ ()) (noconfusionOIDN (toWitness{Q = _ ∈? _} tt))))))))))))


    noconfusion₄ : NoConfusion (ExtensionFields (_≡ OIDs.EKULit) EKUFields) (Sum _ _)
    noconfusion₄ =
      Sum.noconfusion{ExtensionFields (_≡ OIDs.EKULit) EKUFields}
        (noconfusionOIDS λ ())
        (Sum.noconfusion{ExtensionFields (_≡ OIDs.EKULit) EKUFields}
          (noconfusionOIDS λ ())
          (Sum.noconfusion{ExtensionFields (_≡ OIDs.EKULit) EKUFields}
            (noconfusionOIDS λ ())
            (Sum.noconfusion{ExtensionFields (_≡ OIDs.EKULit) EKUFields}
              (noconfusionOIDS λ ())
              (Sum.noconfusion{ExtensionFields (_≡ OIDs.EKULit) EKUFields}
                (noconfusionOIDS λ ())
                (Sum.noconfusion{ExtensionFields (_≡ OIDs.EKULit) EKUFields}
                  (noconfusionOIDS λ ())
                  (Sum.noconfusion{ExtensionFields (_≡ OIDs.EKULit) EKUFields}
                    (noconfusionOIDS λ ())
                    (Sum.noconfusion{ExtensionFields (_≡ OIDs.EKULit) EKUFields}
                      (noconfusionOIDS λ ())
                      (Sum.noconfusion{ExtensionFields (_≡ OIDs.EKULit) EKUFields}
                        (noconfusionOIDS λ ())
                        (Sum.noconfusion{ExtensionFields (_≡ OIDs.EKULit) EKUFields}
                          (noconfusionOIDS λ ()) (noconfusionOIDN (toWitness{Q = _ ∈? _} tt)))))))))))


    noconfusion₅ : NoConfusion (ExtensionFields (_≡ OIDs.BCLit)  BCFields)  (Sum _ _)
    noconfusion₅ =
      Sum.noconfusion{ExtensionFields (_≡ OIDs.BCLit) BCFields}
        (noconfusionOIDS λ ())
        (Sum.noconfusion{ExtensionFields (_≡ OIDs.BCLit) BCFields}
          (noconfusionOIDS λ ())
          (Sum.noconfusion{ExtensionFields (_≡ OIDs.BCLit) BCFields}
            (noconfusionOIDS λ ())
            (Sum.noconfusion{ExtensionFields (_≡ OIDs.BCLit) BCFields}
              (noconfusionOIDS λ ())
              (Sum.noconfusion{ExtensionFields (_≡ OIDs.BCLit) BCFields}
                (noconfusionOIDS λ ())
                (Sum.noconfusion{ExtensionFields (_≡ OIDs.BCLit) BCFields}
                  (noconfusionOIDS λ ())
                  (Sum.noconfusion{ExtensionFields (_≡ OIDs.BCLit) BCFields}
                    (noconfusionOIDS λ ())
                    (Sum.noconfusion{ExtensionFields (_≡ OIDs.BCLit) BCFields}
                      (noconfusionOIDS λ ())
                      (Sum.noconfusion{ExtensionFields (_≡ OIDs.BCLit) BCFields}
                        (noconfusionOIDS λ ()) (noconfusionOIDN (toWitness{Q = _ ∈? _} tt))))))))))


    noconfusion₆ : NoConfusion (ExtensionFields (_≡ OIDs.IANLit) IANFields) (Sum _ _)
    noconfusion₆ =
      Sum.noconfusion{ExtensionFields (_≡ OIDs.IANLit) IANFields}
        (noconfusionOIDS λ ())
        (Sum.noconfusion{ExtensionFields (_≡ OIDs.IANLit) IANFields}
          (noconfusionOIDS λ ())
          (Sum.noconfusion{ExtensionFields (_≡ OIDs.IANLit) IANFields}
            (noconfusionOIDS λ ())
            (Sum.noconfusion{ExtensionFields (_≡ OIDs.IANLit) IANFields}
              (noconfusionOIDS λ ())
              (Sum.noconfusion{ExtensionFields (_≡ OIDs.IANLit) IANFields}
                (noconfusionOIDS λ ())
                (Sum.noconfusion{ExtensionFields (_≡ OIDs.IANLit) IANFields}
                  (noconfusionOIDS λ ())
                  (Sum.noconfusion{ExtensionFields (_≡ OIDs.IANLit) IANFields}
                    (noconfusionOIDS λ ())
                    (Sum.noconfusion{ExtensionFields (_≡ OIDs.IANLit) IANFields}
                      (noconfusionOIDS λ ()) (noconfusionOIDN (toWitness{Q = _ ∈? _} tt)))))))))


    noconfusion₇ : NoConfusion (ExtensionFields (_≡ OIDs.SANLit) SANFields) (Sum _ _)
    noconfusion₇ =
      Sum.noconfusion{ExtensionFields (_≡ OIDs.SANLit) SANFields}
        (noconfusionOIDS λ ())
        (Sum.noconfusion{ExtensionFields (_≡ OIDs.SANLit) SANFields}
          (noconfusionOIDS λ ())
          (Sum.noconfusion{ExtensionFields (_≡ OIDs.SANLit) SANFields}
            (noconfusionOIDS λ ())
            (Sum.noconfusion{ExtensionFields (_≡ OIDs.SANLit) SANFields}
              (noconfusionOIDS λ ())
              (Sum.noconfusion{ExtensionFields (_≡ OIDs.SANLit) SANFields}
                (noconfusionOIDS λ ())
                (Sum.noconfusion{ExtensionFields (_≡ OIDs.SANLit) SANFields}
                  (noconfusionOIDS λ ())
                  (Sum.noconfusion{ExtensionFields (_≡ OIDs.SANLit) SANFields}
                    (noconfusionOIDS λ ()) (noconfusionOIDN (toWitness{Q = _ ∈? _} tt))))))))

    noconfusion₈ : NoConfusion (ExtensionFields (_≡ OIDs.CPOLLit) CertPolFields) (Sum _ _)
    noconfusion₈ =
      Sum.noconfusion{ExtensionFields (_≡ OIDs.CPOLLit) CertPolFields}
        (noconfusionOIDS λ ())
        (Sum.noconfusion{ExtensionFields (_≡ OIDs.CPOLLit) CertPolFields}
          (noconfusionOIDS λ ())
          (Sum.noconfusion{ExtensionFields (_≡ OIDs.CPOLLit) CertPolFields}
            (noconfusionOIDS λ ())
            (Sum.noconfusion{ExtensionFields (_≡ OIDs.CPOLLit) CertPolFields}
              (noconfusionOIDS λ ())
              (Sum.noconfusion{ExtensionFields (_≡ OIDs.CPOLLit) CertPolFields}
                (noconfusionOIDS λ ())
                (Sum.noconfusion{ExtensionFields (_≡ OIDs.CPOLLit) CertPolFields}
                  (noconfusionOIDS λ ()) (noconfusionOIDN (toWitness{Q = _ ∈? _} tt)))))))

    noconfusion₉ : NoConfusion (ExtensionFields (_≡ OIDs.CRLDISTLit) CRLDistFields) (Sum _ _)
    noconfusion₉ =
      Sum.noconfusion{ExtensionFields (_≡ OIDs.CRLDISTLit) CRLDistFields}
        (noconfusionOIDS λ ())
          (Sum.noconfusion{ExtensionFields (_≡ OIDs.CRLDISTLit) CRLDistFields}
          (noconfusionOIDS λ ())
            (Sum.noconfusion{ExtensionFields (_≡ OIDs.CRLDISTLit) CRLDistFields}
              (noconfusionOIDS λ ())
              (Sum.noconfusion{ExtensionFields (_≡ OIDs.CRLDISTLit) CRLDistFields}
                (noconfusionOIDS λ ())
                (Sum.noconfusion{ExtensionFields (_≡ OIDs.CRLDISTLit) CRLDistFields}
                  (noconfusionOIDS λ ()) (noconfusionOIDN (toWitness{Q = _ ∈? _} tt))))))

    noconfusion₁₀ : NoConfusion (ExtensionFields (_≡ OIDs.NCLit) NCFields) (Sum _ _)
    noconfusion₁₀ =
      Sum.noconfusion{ExtensionFields (_≡ OIDs.NCLit) NCFields}
        (noconfusionOIDS λ ())
        (Sum.noconfusion{ExtensionFields (_≡ OIDs.NCLit) NCFields}
          (noconfusionOIDS λ ())
          (Sum.noconfusion{ExtensionFields (_≡ OIDs.NCLit) NCFields}
            (noconfusionOIDS λ ())
            (Sum.noconfusion{ExtensionFields (_≡ OIDs.NCLit) NCFields}
              (noconfusionOIDS λ ()) (noconfusionOIDN (toWitness{Q = _ ∈? _} tt)))))

    noconfusion₁₁ : NoConfusion (ExtensionFields (_≡ OIDs.PCLit) PCFields) (Sum _ _)
    noconfusion₁₁ =
      Sum.noconfusion{ExtensionFields (_≡ OIDs.PCLit) PCFields}
        (noconfusionOIDS λ ())
        (Sum.noconfusion{ExtensionFields (_≡ OIDs.PCLit) PCFields}
          (noconfusionOIDS λ ())
          (Sum.noconfusion{ExtensionFields (_≡ OIDs.PCLit) PCFields}
            (noconfusionOIDS λ ()) (noconfusionOIDN (toWitness{Q = _ ∈? _} tt))))

    noconfusion₁₂ : NoConfusion (ExtensionFields (_≡ OIDs.PMLit) PMFields) (Sum _ _)
    noconfusion₁₂ =
      Sum.noconfusion{ExtensionFields (_≡ OIDs.PMLit) PMFields}
        (noconfusionOIDS λ ())
          (Sum.noconfusion{ExtensionFields (_≡ OIDs.PMLit) PMFields}
            (noconfusionOIDS λ ()) (noconfusionOIDN (toWitness{Q = _ ∈? _} tt)))

    noconfusion₁₃ : NoConfusion (ExtensionFields (_≡ OIDs.INAPLit) INAPFields) (Sum _ _)
    noconfusion₁₃ =
      Sum.noconfusion{ExtensionFields (_≡ OIDs.INAPLit) INAPFields}
        (noconfusionOIDS λ ()) (noconfusionOIDN (toWitness{Q = _ ∈? _} tt))

    noconfusion₀ : NoConfusion (ExtensionFields (_≡ OIDs.AIALit) AIAFields) (ExtensionFields _ _)
    noconfusion₀ = noconfusionOIDN (toWitness{Q = _ ∈? _} tt)

    ua : Unambiguous (λ x → False (x ∈? supportedExtensions))
    ua = T-unique

  @0 nonmalleable : NonMalleable RawSelectExtn
  nonmalleable = Iso.nonmalleable iso RawSelectExtnRep nm
    where
    RawRep₀ = RawSum (RawExtensionFields RawAIAFields) (RawExtensionFields RawOctetString)
    RawRep₁ = RawSum (RawExtensionFields RawINAPFields) RawRep₀
    RawRep₂ = RawSum (RawExtensionFields RawPMFields) RawRep₁
    RawRep₃ = RawSum (RawExtensionFields RawPCFields) RawRep₂
    RawRep₄ = RawSum (RawExtensionFields RawNCFields) RawRep₃
    RawRep₅ = RawSum (RawExtensionFields RawCRLDistFields) RawRep₄
    RawRep₆ = RawSum (RawExtensionFields RawCertPolFields) RawRep₅
    RawRep₇ = RawSum (RawExtensionFields RawSANFields) RawRep₆
    RawRep₈ = RawSum (RawExtensionFields RawIANFields) RawRep₇
    RawRep₉ = RawSum (RawExtensionFields RawBCFields) RawRep₈
    RawRep₁₀ = RawSum (RawExtensionFields RawEKUFields) RawRep₉
    RawRep₁₁ = RawSum (RawExtensionFields RawKUFields) RawRep₁₀
    RawRep₁₂ = RawSum (RawExtensionFields RawSKIFields) RawRep₁₁
    RawRep = RawSum (RawExtensionFields{P = (_≡ OIDs.AKILit)} RawAKIFields) RawRep₁₂
                           
    nm : NonMalleable RawSelectExtnRep
    nm = Sum.nonmalleable{ra = RawExtensionFields RawAKIFields}{rb = RawRep₁₂} ((Fields.nonmalleable ≡-unique AKI.nonmalleable))
      (Sum.nonmalleable{ra = RawExtensionFields RawSKIFields}{rb = RawRep₁₁} ((Fields.nonmalleable ≡-unique SKI.nonmalleable))
      (Sum.nonmalleable{ra = RawExtensionFields RawKUFields}{rb = RawRep₁₀} ((Fields.nonmalleable ≡-unique KU.nonmalleable))
      (Sum.nonmalleable{ra = RawExtensionFields RawEKUFields}{rb = RawRep₉} ((Fields.nonmalleable ≡-unique EKU.nonmalleable))
      (Sum.nonmalleable{ra = RawExtensionFields RawBCFields}{rb = RawRep₈} ((Fields.nonmalleable ≡-unique BC.nonmalleable))
      (Sum.nonmalleable{ra = RawExtensionFields RawIANFields}{rb = RawRep₇} ((Fields.nonmalleable ≡-unique IAN.nonmalleable))
      (Sum.nonmalleable{ra = RawExtensionFields RawSANFields}{rb = RawRep₆} ((Fields.nonmalleable ≡-unique SAN.nonmalleable))
      (Sum.nonmalleable{ra = RawExtensionFields RawCertPolFields}{rb = RawRep₅} ((Fields.nonmalleable ≡-unique CertPolicy.nonmalleable))
      (Sum.nonmalleable{ra = RawExtensionFields RawCRLDistFields}{rb = RawRep₄} ((Fields.nonmalleable ≡-unique CRLDistPoint.nonmalleable))
      (Sum.nonmalleable{ra = RawExtensionFields RawNCFields}{rb = RawRep₃} ((Fields.nonmalleable ≡-unique NC.nonmalleable))
      (Sum.nonmalleable{ra = RawExtensionFields RawPCFields}{rb = RawRep₂} ((Fields.nonmalleable ≡-unique PC.nonmalleable))
      (Sum.nonmalleable{ra = RawExtensionFields RawPMFields}{rb = RawRep₁} ((Fields.nonmalleable ≡-unique PM.nonmalleable))
      (Sum.nonmalleable{ra = RawExtensionFields RawINAPFields}{rb = RawRep₀} ((Fields.nonmalleable ≡-unique INAP.nonmalleable))
      (Sum.nonmalleable{ra = RawExtensionFields RawAIAFields}{rb = RawExtensionFields RawOctetString}
                        (Fields.nonmalleable ≡-unique AIA.nonmalleable)
                         (Fields.nonmalleable T-unique OctetString.nonmalleable))))))))))))))

@0 unambiguous : Unambiguous Extensions
unambiguous =
    TLV.unambiguous (TLV.unambiguous
      (SequenceOf.Bounded.unambiguous
        (TLV.unambiguous Select.unambiguous)
        TLV.nonempty TLV.nosubstrings))

@0 nonmalleable : NonMalleable RawExtensions
nonmalleable = TLV.nonmalleable (TLV.nonmalleable
                 (SequenceOf.Bounded.nonmalleable
                   TLV.nonempty TLV.nosubstrings (TLV.nonmalleable
                     Select.nonmalleable)))
