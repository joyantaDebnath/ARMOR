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
open import Armor.Data.X509.Extension.Properties
open import Armor.Data.X509.Extension.TCB
open import Armor.Data.X509.GeneralNames
open import Armor.Data.X509.GeneralNames.GeneralName
open import Armor.Data.X690-DER.BitString
open import Armor.Data.X690-DER.Boool
open import Armor.Data.X690-DER.Default
open import Armor.Data.X690-DER.Int
open import Armor.Data.X690-DER.OID
open import Armor.Data.X690-DER.OctetString
open import Armor.Data.X690-DER.TLV
open import Armor.Data.X690-DER.SequenceOf
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Definitions
import      Armor.Grammar.Option
import      Armor.Grammar.Parallel
import      Armor.Grammar.Properties
import      Armor.Grammar.Seq
import      Armor.Grammar.Sum
open import Armor.Prelude

module Armor.Data.X509.Extension.Eq where

open ≡-Reasoning

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Option      UInt8
open Armor.Grammar.Parallel    UInt8
open Armor.Grammar.Properties  UInt8
open Armor.Grammar.Seq         UInt8
open Armor.Grammar.Sum         UInt8

eq≋Field : ∀ {@0 P : List UInt8 → Set} {A : @0 List UInt8 → Set} → (∀ {@0 bs} → Unique (P bs)) → ⦃ _ : Eq≋ A ⦄ → Eq≋ (ExtensionFields P A)
eq≋Field eqP =
  Iso.isoEq≋ Fields.iso
    (Seq.eq≋&ₚ
      (Parallel.eq≋Σₚ it λ _ →
        record { _≟_ = λ x y → yes (erased-unique eqP x y) })
      (Seq.eq≋&ₚ (Default.eq≋ _) it))

instance
  eq≋ : Eq≋ SelectExtn
  eq≋ =
    Iso.isoEq≋ Select.iso
             (Sum.sumEq≋ ⦃ eq₁ = eq≋Field λ {@0 xs} a b → ‼ ≡-unique a b ⦄
      ⦃ eq₂ = Sum.sumEq≋ ⦃ eq₁ = eq≋Field λ a b → ‼ ≡-unique a b ⦄
      ⦃ eq₂ = Sum.sumEq≋ ⦃ eq₁ = eq≋Field λ a b → ‼ ≡-unique a b ⦄
      ⦃ eq₂ = Sum.sumEq≋ ⦃ eq₁ = eq≋Field (λ a b → ‼ ≡-unique a b) ⦄
      ⦃ eq₂ = Sum.sumEq≋ ⦃ eq₁ = eq≋Field λ a b → ‼ ≡-unique a b ⦄
      ⦃ eq₂ = Sum.sumEq≋ ⦃ eq₁ = eq≋Field λ a b → ‼ ≡-unique a b  ⦄
      ⦃ eq₂ = Sum.sumEq≋ ⦃ eq₁ = eq≋Field λ a b → ‼ ≡-unique a b  ⦄
      ⦃ eq₂ = Sum.sumEq≋ ⦃ eq₁ = eq≋Field λ a b → ‼ ≡-unique a b ⦄
      ⦃ eq₂ = Sum.sumEq≋ ⦃ eq₁ = eq≋Field λ a b → ‼ ≡-unique a b ⦄
      ⦃ eq₂ = Sum.sumEq≋ ⦃ eq₁ = eq≋Field λ a b → ‼ ≡-unique a b ⦄
      ⦃ eq₂ = Sum.sumEq≋ ⦃ eq₁ = eq≋Field λ a b → ‼ ≡-unique a b ⦄
      ⦃ eq₂ = Sum.sumEq≋ ⦃ eq₁ = eq≋Field λ a b → ‼ ≡-unique a b ⦄
      ⦃ eq₂ = Sum.sumEq≋ ⦃ eq₁ = eq≋Field λ a b → ‼ ≡-unique a b ⦄
      ⦃ eq₂ = Sum.sumEq≋ ⦃ eq₁ = eq≋Field λ a b → ‼ ≡-unique a b ⦄
      ⦃ eq₂ = eq≋Field (λ p₁ p₂ → ‼ T-unique p₁ p₂) ⦄ ⦄ ⦄ ⦄ ⦄ ⦄ ⦄ ⦄ ⦄ ⦄ ⦄ ⦄ ⦄ ⦄)
    where
    instance
      e₁ : Eq≋ (NonEmptySequenceOf OID)
      e₁ = SequenceOf.BoundedSequenceOfEq≋

      e₂ : Eq≋ (NonEmptySequenceOf CertPolicy.PolicyInformation)
      e₂ = SequenceOf.BoundedSequenceOfEq≋

      e₃ : Eq≋ (NonEmptySequenceOf CRLDistPoint.DistPoint)
      e₃ = SequenceOf.BoundedSequenceOfEq≋

      e₄ : Eq≋ (NonEmptySequenceOf PolicyMap)
      e₄ = SequenceOf.BoundedSequenceOfEq≋

      e₅ : Eq≋ (NonEmptySequenceOf AIA.AccessDesc)
      e₅ = SequenceOf.BoundedSequenceOfEq≋
