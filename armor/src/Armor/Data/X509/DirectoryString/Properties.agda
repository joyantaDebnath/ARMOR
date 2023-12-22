open import Armor.Binary
import      Armor.Grammar.Sum
open import Armor.Data.Unicode
open import Armor.Data.X690-DER.Strings.IA5String
open import Armor.Data.X690-DER.Strings.PrintableString
open import Armor.Data.X509.DirectoryString.TCB
open import Armor.Data.X690-DER
import      Armor.Grammar.Definitions
import      Armor.Grammar.IList
import      Armor.Grammar.Parallel
open import Armor.Prelude
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Armor.Data.X509.DirectoryString.Properties where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.IList       UInt8
open Armor.Grammar.Parallel    UInt8
open Armor.Grammar.Sum         UInt8

nosubstrings : NoSubstrings DirectoryString
nosubstrings x (teletexString x₁) (teletexString x₂)      = ‼ (Parallel.nosubstrings₁ TLV.nosubstrings x x₁ x₂)
nosubstrings x (teletexString x₁) (printableString x₂)    = ⊥-elim (Parallel.noconfusionΣₚ₁ (TLV.noconfusion λ ()) x x₁ x₂)
nosubstrings x (teletexString x₁) (universalString x₂)    = ⊥-elim (Parallel.noconfusionΣₚ₁ (TLV.noconfusion λ ()) x x₁ x₂)
nosubstrings x (teletexString x₁) (utf8String x₂)         = ⊥-elim (Parallel.noconfusionΣₚ₁ (TLV.noconfusion λ ()) x x₁ x₂)
nosubstrings x (teletexString x₁) (bmpString x₂)          = ⊥-elim (Parallel.noconfusionΣₚ₁ (TLV.noconfusion λ ()) x x₁ x₂)
nosubstrings x (printableString x₁) (teletexString x₂)    = ⊥-elim (Parallel.noconfusionΣₚ₁ (TLV.noconfusion λ ()) x x₁ x₂)
nosubstrings x (printableString x₁) (printableString x₂)  = ‼ (Parallel.nosubstrings₁ TLV.nosubstrings x x₁ x₂)
nosubstrings x (printableString x₁) (universalString x₂)  = ⊥-elim (Parallel.noconfusionΣₚ₁ (TLV.noconfusion λ ()) x x₁ x₂)
nosubstrings x (printableString x₁) (utf8String x₂)       = ⊥-elim (Parallel.noconfusionΣₚ₁ (TLV.noconfusion λ ()) x x₁ x₂)
nosubstrings x (printableString x₁) (bmpString x₂)        = ⊥-elim (Parallel.noconfusionΣₚ₁ (TLV.noconfusion λ ()) x x₁ x₂)
nosubstrings x (universalString x₁) (teletexString x₂)    = ⊥-elim (Parallel.noconfusionΣₚ₁ (TLV.noconfusion λ ()) x x₁ x₂)
nosubstrings x (universalString x₁) (printableString x₂)  = ⊥-elim (Parallel.noconfusionΣₚ₁ (TLV.noconfusion λ ()) x x₁ x₂)
nosubstrings x (universalString x₁) (universalString x₂)  = ‼ (Parallel.nosubstrings₁ TLV.nosubstrings x x₁ x₂)
nosubstrings x (universalString x₁) (utf8String x₂)       = ⊥-elim (Parallel.noconfusionΣₚ₁ (TLV.noconfusion λ ()) x x₁ x₂)
nosubstrings x (universalString x₁) (bmpString x₂)        = ⊥-elim (Parallel.noconfusionΣₚ₁ (TLV.noconfusion λ ()) x x₁ x₂)
nosubstrings x (utf8String x₁) (teletexString x₂)         = ⊥-elim (Parallel.noconfusionΣₚ₁ (TLV.noconfusion λ ()) x x₁ x₂)
nosubstrings x (utf8String x₁) (printableString x₂)       = ⊥-elim (Parallel.noconfusionΣₚ₁ (TLV.noconfusion λ ()) x x₁ x₂)
nosubstrings x (utf8String x₁) (universalString x₂)       = ⊥-elim (Parallel.noconfusionΣₚ₁ (TLV.noconfusion λ ()) x x₁ x₂)
nosubstrings x (utf8String x₁) (utf8String x₂)            = ‼ (Parallel.nosubstrings₁ TLV.nosubstrings x x₁ x₂)
nosubstrings x (utf8String x₁) (bmpString x₂)             = ⊥-elim (Parallel.noconfusionΣₚ₁ (TLV.noconfusion λ ()) x x₁ x₂)
nosubstrings x (bmpString x₁) (teletexString x₂)          = ⊥-elim (Parallel.noconfusionΣₚ₁ (TLV.noconfusion λ ()) x x₁ x₂)
nosubstrings x (bmpString x₁) (printableString x₂)        = ⊥-elim (Parallel.noconfusionΣₚ₁ (TLV.noconfusion λ ()) x x₁ x₂)
nosubstrings x (bmpString x₁) (universalString x₂)        = ⊥-elim (Parallel.noconfusionΣₚ₁ (TLV.noconfusion λ ()) x x₁ x₂)
nosubstrings x (bmpString x₁) (utf8String x₂)             = ⊥-elim (Parallel.noconfusionΣₚ₁ (TLV.noconfusion λ ()) x x₁ x₂)
nosubstrings x (bmpString x₁) (bmpString x₂)              = ‼ (Parallel.nosubstrings₁ TLV.nosubstrings x x₁ x₂)

@0 noconfusion₁ : NoConfusion (Σₚ TeletexString TLVNonEmptyVal)
                    (Sum (Σₚ PrintableString TLVNonEmptyVal)
                    (Sum (Σₚ UniversalString TLVNonEmptyVal)
                    (Sum (Σₚ UTF8String TLVNonEmptyVal)
                         (Σₚ BMPString TLVNonEmptyVal))))
noconfusion₁ x x₁ (Sum.inj₁ x₂) = Parallel.noconfusionΣₚ₁ (TLV.noconfusion (λ ())) x x₁ x₂
noconfusion₁ x x₁ (Sum.inj₂ (Sum.inj₁ x₂)) = Parallel.noconfusionΣₚ₁ (TLV.noconfusion (λ ())) x x₁ x₂
noconfusion₁ x x₁ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x₂))) = Parallel.noconfusionΣₚ₁ (TLV.noconfusion (λ ())) x x₁ x₂
noconfusion₁ x x₁ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ x₂))) = Parallel.noconfusionΣₚ₁ (TLV.noconfusion (λ ())) x x₁ x₂

@0 noconfusion₂ : NoConfusion (Σₚ PrintableString TLVNonEmptyVal)
                              (Sum (Σₚ UniversalString TLVNonEmptyVal)
                              (Sum (Σₚ UTF8String      TLVNonEmptyVal)
                                   (Σₚ BMPString       TLVNonEmptyVal)))
noconfusion₂ x x₁ (Sum.inj₁ x₂) = Parallel.noconfusionΣₚ₁ (TLV.noconfusion (λ ())) x x₁ x₂
noconfusion₂ x x₁ (Sum.inj₂ (Sum.inj₁ x₂)) =  Parallel.noconfusionΣₚ₁ (TLV.noconfusion (λ ())) x x₁ x₂
noconfusion₂ x x₁ (Sum.inj₂ (Sum.inj₂ x₂)) =  Parallel.noconfusionΣₚ₁ (TLV.noconfusion (λ ())) x x₁ x₂

@0 noconfusion₃ : NoConfusion (Σₚ UniversalString TLVNonEmptyVal) (Sum (Σₚ UTF8String TLVNonEmptyVal) (Σₚ BMPString TLVNonEmptyVal))
noconfusion₃ x x₁ (Sum.inj₁ x₂) = Parallel.noconfusionΣₚ₁ (TLV.noconfusion (λ ())) x x₁ x₂
noconfusion₃ x x₁ (Sum.inj₂ x₂) = Parallel.noconfusionΣₚ₁ (TLV.noconfusion (λ ())) x x₁ x₂

iso : Iso DirectoryStringRep DirectoryString
proj₁ iso = equivalentDirectoryString
proj₁ (proj₂ iso) (Sum.inj₁ x) = refl
proj₁ (proj₂ iso) (Sum.inj₂ (Sum.inj₁ x)) = refl
proj₁ (proj₂ iso) (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x))) = refl
proj₁ (proj₂ iso) (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x)))) = refl
proj₁ (proj₂ iso) (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ x)))) = refl
proj₂ (proj₂ iso) (teletexString x) = refl
proj₂ (proj₂ iso) (printableString x) = refl
proj₂ (proj₂ iso) (universalString x) = refl
proj₂ (proj₂ iso) (utf8String x) = refl
proj₂ (proj₂ iso) (bmpString x) = refl

@0 nonmalleable : NonMalleable RawDirectoryString
nonmalleable =
  Iso.nonmalleable iso RawDirectoryStringRep nm
  where
  nm : NonMalleable RawDirectoryStringRep
  nm =
     Sum.nonmalleable (Parallel.nonmalleable₁ RawTeletexString   TeletexString.nonmalleable   λ _ → ≤-unique)
    (Sum.nonmalleable (Parallel.nonmalleable₁ RawPrintableString PrintableString.nonmalleable λ _ → ≤-unique)
    (Sum.nonmalleable (Parallel.nonmalleable₁ RawUniversalString UniversalString.nonmalleable λ _ → ≤-unique)
    (Sum.nonmalleable (Parallel.nonmalleable₁ RawUTF8String      UTF8String.nonmalleable      λ _ → ≤-unique)
                      (Parallel.nonmalleable₁ RawBMPString       BMPString.nonmalleable       λ _ → ≤-unique))))
 
@0 unambiguous : Unambiguous DirectoryString
unambiguous = Iso.unambiguous iso
  (Sum.unambiguous (TLV.NonEmptyVal.unambiguous OctetString.unambiguousValue)
    (Sum.unambiguous
      (TLV.NonEmptyVal.unambiguous
        (IList.unambiguous
          PrintableString.Char.unambiguous
          PrintableString.Char.nonempty
          PrintableString.Char.nosubstrings))
      (Sum.unambiguous (TLV.NonEmptyVal.unambiguous UTF32.unambiguous)
        (Sum.unambiguous (TLV.NonEmptyVal.unambiguous UTF8.unambiguous)
          (TLV.NonEmptyVal.unambiguous
            (IList.unambiguous
              UTF16.BMP.unambiguous UTF16.BMP.nonempty UTF16.BMP.nosubstrings))
          (Parallel.noconfusionΣₚ₁ (TLV.noconfusion λ ())))
        noconfusion₃)
      noconfusion₂)
    noconfusion₁)
