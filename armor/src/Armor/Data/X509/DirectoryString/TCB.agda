open import Armor.Binary
open import Armor.Data.X690-DER.Strings.BMPString.TCB
open import Armor.Data.X690-DER.Strings.IA5String.TCB
open import Armor.Data.X690-DER.Strings.PrintableString.TCB
open import Armor.Data.X690-DER.Strings.TeletexString.TCB
open import Armor.Data.X690-DER.Strings.UTF8String.TCB
open import Armor.Data.X690-DER.Strings.UniversalString.TCB
open import Armor.Data.X690-DER.TLV.TCB
import      Armor.Grammar.Definitions
import      Armor.Grammar.Parallel.TCB
import      Armor.Grammar.Sum.TCB
open import Armor.Prelude

module Armor.Data.X509.DirectoryString.TCB where

open Armor.Grammar.Definitions              UInt8
open Armor.Grammar.Parallel.TCB             UInt8
open Armor.Grammar.Sum.TCB                  UInt8

-- https://datatracker.ietf.org/doc/html/rfc5280#section-4.1.2.4
--    DirectoryString ::= CHOICE {
--          teletexString           TeletexString (SIZE (1..MAX)),
--          printableString         PrintableString (SIZE (1..MAX)),
--          universalString         UniversalString (SIZE (1..MAX)),
--          utf8String              UTF8String (SIZE (1..MAX)),
--          bmpString               BMPString (SIZE (1..MAX)) }
         
data DirectoryString : @0 List UInt8 → Set where
  teletexString : ∀ {@0 bs} → Σₚ TeletexString TLVNonEmptyVal bs → DirectoryString bs
  printableString : ∀ {@0 bs} → Σₚ PrintableString TLVNonEmptyVal bs → DirectoryString bs
  universalString : ∀ {@0 bs} → Σₚ UniversalString TLVNonEmptyVal bs → DirectoryString bs
  utf8String : ∀ {@0 bs} → Σₚ UTF8String TLVNonEmptyVal bs → DirectoryString bs
  bmpString  : ∀ {@0 bs} → Σₚ BMPString  TLVNonEmptyVal bs → DirectoryString bs

DirectoryStringRep =
  (Sum (Σₚ TeletexString   TLVNonEmptyVal)
  (Sum (Σₚ PrintableString TLVNonEmptyVal)
  (Sum (Σₚ UniversalString TLVNonEmptyVal)
  (Sum (Σₚ UTF8String      TLVNonEmptyVal)
       (Σₚ BMPString       TLVNonEmptyVal)))))

equivalentDirectoryString : Equivalent DirectoryStringRep DirectoryString
proj₁ equivalentDirectoryString (Sum.inj₁ x) = teletexString x
proj₁ equivalentDirectoryString (Sum.inj₂ (Sum.inj₁ x)) = printableString x
proj₁ equivalentDirectoryString (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x))) = universalString x
proj₁ equivalentDirectoryString (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x)))) = utf8String x
proj₁ equivalentDirectoryString (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ x)))) = bmpString x
proj₂ equivalentDirectoryString (teletexString x) = Sum.inj₁ x
proj₂ equivalentDirectoryString (printableString x) = Sum.inj₂ (Sum.inj₁ x)
proj₂ equivalentDirectoryString (universalString x) = Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x))
proj₂ equivalentDirectoryString (utf8String x) = Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x)))
proj₂ equivalentDirectoryString (bmpString x) = Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ x)))

RawDirectoryStringRep : Raw DirectoryStringRep
RawDirectoryStringRep =
  (RawSum (RawΣₚ₁ RawTeletexString TLVNonEmptyVal)
  (RawSum (RawΣₚ₁ RawPrintableString TLVNonEmptyVal)
  (RawSum (RawΣₚ₁ RawUniversalString TLVNonEmptyVal)
  (RawSum (RawΣₚ₁ RawUTF8String TLVNonEmptyVal)
          (RawΣₚ₁ RawBMPString TLVNonEmptyVal)))))

RawDirectoryString : Raw DirectoryString
RawDirectoryString = Iso.raw equivalentDirectoryString RawDirectoryStringRep
