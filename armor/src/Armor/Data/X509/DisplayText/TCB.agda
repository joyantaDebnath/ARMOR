open import Armor.Binary
open import Armor.Data.Unicode.UTF8.TCB
open import Armor.Data.Unicode.UTF16.TCB
  renaming (size to sizeBMP)
open import Armor.Data.X690-DER.TLV.TCB
open import Armor.Data.X690-DER.Strings.BMPString.TCB
open import Armor.Data.X690-DER.Strings.IA5String.TCB
open import Armor.Data.X690-DER.Strings.UTF8String.TCB
open import Armor.Data.X690-DER.Strings.VisibleString.TCB
import      Armor.Grammar.Definitions
import      Armor.Grammar.Parallel.TCB
import      Armor.Grammar.Sum.TCB
open import Armor.Prelude

module Armor.Data.X509.DisplayText.TCB where

open Armor.Grammar.Definitions   UInt8
open Armor.Grammar.Parallel.TCB  UInt8
open Armor.Grammar.Sum.TCB       UInt8

-- https://datatracker.ietf.org/doc/html/rfc5280#section-4.2.1.4
--    DisplayText ::= CHOICE {
--         ia5String        IA5String      (SIZE (1..200)),
--         visibleString    VisibleString  (SIZE (1..200)),
--         bmpString        BMPString      (SIZE (1..200)),
--         utf8String       UTF8String     (SIZE (1..200)) }
        
data DisplayText : @0 List UInt8 → Set where
  ia5String     : ∀ {@0 bs} → Σₚ IA5String     (TLVSizeBounded IA5StringValue.size     1 200) bs → DisplayText bs
  visibleString : ∀ {@0 bs} → Σₚ VisibleString (TLVSizeBounded VisibleStringValue.size 1 200) bs → DisplayText bs
  bmpString     : ∀ {@0 bs} → Σₚ BMPString     (TLVSizeBounded sizeBMP                 1 200) bs → DisplayText bs
  utf8String    : ∀ {@0 bs} → Σₚ UTF8String    (TLVSizeBounded UTF8.size               1 200) bs → DisplayText bs

DisplayTextRep : @0 List UInt8 → Set
DisplayTextRep =
  (Sum (Σₚ IA5String     (TLVSizeBounded IA5StringValue.size 1 200))
  (Sum (Σₚ VisibleString (TLVSizeBounded VisibleStringValue.size 1 200))
  (Sum (Σₚ BMPString     (TLVSizeBounded sizeBMP 1 200))
       (Σₚ UTF8String    (TLVSizeBounded UTF8.size 1 200)))))

equivalent : Equivalent DisplayTextRep DisplayText
proj₁ equivalent (Sum.inj₁ x) = ia5String x
proj₁ equivalent (Sum.inj₂ (Sum.inj₁ x)) = visibleString x
proj₁ equivalent (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x))) = bmpString x
proj₁ equivalent (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ x))) = utf8String x
proj₂ equivalent (ia5String x) = inj₁ x
proj₂ equivalent (visibleString x) = inj₂ (inj₁ x)
proj₂ equivalent (bmpString x) = inj₂ (inj₂ (inj₁ x))
proj₂ equivalent (utf8String x) = inj₂ (inj₂ (inj₂ x))

RawDisplayTextRep : Raw DisplayTextRep
RawDisplayTextRep =
   RawSum (RawΣₚ₁ RawIA5String _)
  (RawSum (RawΣₚ₁ RawVisibleString _)
  (RawSum (RawΣₚ₁ RawBMPString _)
          (RawΣₚ₁ RawUTF8String _)))

RawDisplayText : Raw DisplayText
RawDisplayText = Iso.raw equivalent RawDisplayTextRep

