{-# OPTIONS --sized-types #-}

open import Data.Nat.DivMod
import      Armor.Binary
open import Armor.Data.X509
import      Armor.Grammar.Definitions
open import Armor.Grammar.IList
import      Armor.Grammar.Parallel
import      Armor.Grammar.Sum
open import Armor.Prelude

open import Armor.Data.Unicode
open import Armor.Data.Unicode.UTF8.Trie
open import Armor.Data.X509.Semantic.StringPrep.Common

import      Data.Nat.Properties as Nat
open import Data.These.Base

open import Armor.Data.X509.Semantic.StringPrep.ExcludeRange

module Armor.Data.X509.Semantic.StringPrep.ExecDS where

open Armor.Binary
open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Parallel    UInt8

-- https://datatracker.ietf.org/doc/html/rfc4518#section-2.1
   -- Each non-Unicode string value is transcoded to Unicode.

   -- PrintableString [X.680] values are transcoded directly to Unicode.

   -- UniversalString, UTF8String, and bmpString [X.680] values need not be
   -- transcoded as they are Unicode-based strings (in the case of
   -- bmpString, a subset of Unicode).

   -- TeletexString [X.680] values are transcoded to Unicode.  As there is
   -- no standard for mapping TeletexString values to Unicode, the mapping
   -- is left a local matter.

   -- For these and other reasons, use of TeletexString is NOT RECOMMENDED.

   -- The output is the transcoded string.

TranscodeDS : ∀ {@0 bs} → DirectoryString bs → String ⊎ Exists─ (List UInt8) Unicode
TranscodeDS (teletexString x) = inj₁ "error in stringprep : teletexstring not supported" 
TranscodeDS (printableString (mk×ₚ (mkTLV len val len≡ bs≡₁) sndₚ₁≡)) = inj₂ (_ , (utf8 (proj₂ (helper val))))
  where
  helper :  ∀ {@0 bs} → IList UInt8 PrintableString.PrintableStringChar bs  → Exists─ (List UInt8) UTF8
  helper nil = _ , nil
  helper (cons (mkIListCons (PrintableString.mkPrintableStringChar .(# 32) PrintableString.space bs≡₁) tail₁ bs≡)) = _ , cons (mkIListCons (utf81 (mkUTF8Char1 (# 32) (toWitness {Q = 32 <? 128 } tt) bs≡₁)) (proj₂ (helper tail₁)) refl)
  helper (cons (mkIListCons (PrintableString.mkPrintableStringChar .(# 39) PrintableString.apostrophe bs≡₁) tail₁ bs≡)) = _ , cons (mkIListCons (utf81 (mkUTF8Char1 (# 39) (toWitness {Q = 39 <? 128 } tt) bs≡₁)) (proj₂ (helper tail₁)) refl)
  helper (cons (mkIListCons (PrintableString.mkPrintableStringChar .(# 40) PrintableString.leftParen bs≡₁) tail₁ bs≡)) = _ , cons (mkIListCons (utf81 (mkUTF8Char1 (# 40) (toWitness {Q = 40 <? 128 } tt) bs≡₁)) (proj₂ (helper tail₁)) refl)
  helper (cons (mkIListCons (PrintableString.mkPrintableStringChar .(# 41) PrintableString.rightParen bs≡₁) tail₁ bs≡)) = _ , cons (mkIListCons (utf81 (mkUTF8Char1 (# 41) (toWitness {Q = 41 <? 128 } tt) bs≡₁)) (proj₂ (helper tail₁)) refl)
  helper (cons (mkIListCons (PrintableString.mkPrintableStringChar .(# 43) PrintableString.plus bs≡₁) tail₁ bs≡)) = _ , cons (mkIListCons (utf81 (mkUTF8Char1 (# 43) (toWitness {Q = 43 <? 128 } tt) bs≡₁)) (proj₂ (helper tail₁)) refl)
  helper (cons (mkIListCons (PrintableString.mkPrintableStringChar .(# 44) PrintableString.comma bs≡₁) tail₁ bs≡)) = _ , cons (mkIListCons (utf81 (mkUTF8Char1 (# 44) (toWitness {Q = 44 <? 128 } tt) bs≡₁)) (proj₂ (helper tail₁)) refl)
  helper (cons (mkIListCons (PrintableString.mkPrintableStringChar .(# 45) PrintableString.hyphen bs≡₁) tail₁ bs≡)) = _ , cons (mkIListCons (utf81 (mkUTF8Char1 (# 45) (toWitness {Q = 45 <? 128 } tt) bs≡₁)) (proj₂ (helper tail₁)) refl)
  helper (cons (mkIListCons (PrintableString.mkPrintableStringChar .(# 46) PrintableString.period bs≡₁) tail₁ bs≡)) = _ , cons (mkIListCons (utf81 (mkUTF8Char1 (# 46) (toWitness {Q = 46 <? 128 } tt) bs≡₁)) (proj₂ (helper tail₁)) refl)
  helper (cons (mkIListCons (PrintableString.mkPrintableStringChar .(# 47) PrintableString.fslash bs≡₁) tail₁ bs≡)) = _ , cons (mkIListCons (utf81 (mkUTF8Char1 (# 47) (toWitness {Q = 47 <? 128 } tt) bs≡₁)) (proj₂ (helper tail₁)) refl)
  helper (cons (mkIListCons (PrintableString.mkPrintableStringChar c (PrintableString.numbers (fst , snd)) bs≡₁) tail₁ bs≡)) = _ , cons (mkIListCons (utf81 (mkUTF8Char1 c (Nat.≤-trans (s≤s snd) (toWitness {Q = 57 <? 128} tt)) bs≡₁)) (proj₂ (helper tail₁)) refl)
  helper (cons (mkIListCons (PrintableString.mkPrintableStringChar .(# 58) PrintableString.colon bs≡₁) tail₁ bs≡)) = _ , cons (mkIListCons (utf81 (mkUTF8Char1 (# 58) (toWitness {Q = 58 <? 128 } tt) bs≡₁)) (proj₂ (helper tail₁)) refl)
  helper (cons (mkIListCons (PrintableString.mkPrintableStringChar .(# 61) PrintableString.equals bs≡₁) tail₁ bs≡)) = _ , cons (mkIListCons (utf81 (mkUTF8Char1 (# 61) (toWitness {Q = 61 <? 128 } tt) bs≡₁)) (proj₂ (helper tail₁)) refl)
  helper (cons (mkIListCons (PrintableString.mkPrintableStringChar .(# 63) PrintableString.question bs≡₁) tail₁ bs≡)) = _ , cons (mkIListCons (utf81 (mkUTF8Char1 (# 63) (toWitness {Q = 63 <? 128 } tt) bs≡₁)) (proj₂ (helper tail₁)) refl)
  helper (cons (mkIListCons (PrintableString.mkPrintableStringChar c (PrintableString.uppers (fst , snd)) bs≡₁) tail₁ bs≡)) = _ , cons (mkIListCons (utf81 (mkUTF8Char1 c (Nat.≤-trans (s≤s snd) (toWitness {Q = 90 <? 128} tt)) bs≡₁)) (proj₂ (helper tail₁)) refl)
  helper (cons (mkIListCons (PrintableString.mkPrintableStringChar c (PrintableString.lowers (fst , snd)) bs≡₁) tail₁ bs≡)) = _ , cons (mkIListCons (utf81 (mkUTF8Char1 c (Nat.≤-trans (s≤s snd) (toWitness {Q = 122 <? 128} tt)) bs≡₁)) (proj₂ (helper tail₁)) refl)
TranscodeDS (universalString (mk×ₚ (mkTLV len val len≡ bs≡₁) sndₚ₁)) = inj₂ (_ , utf32 val)
TranscodeDS (utf8String (mk×ₚ (mkTLV len val len≡ bs≡₁) sndₚ₁)) = inj₂ (_ , utf8 val)
TranscodeDS (bmpString (mk×ₚ (mkTLV len val len≡ bs≡₁) sndₚ₁)) = inj₂ (_ , utf16 val)

-- https://datatracker.ietf.org/doc/html/rfc4518#section-2
   -- The following six-step process SHALL be applied to each presented and
   -- attribute value in preparation for character string matching rule
   -- evaluation.

   --    1) Transcode
   --    2) Map
   --    3) Normalize
   --    4) Prohibit
   --    5) Check bidi
   --    6) Insignificant Character Handling

-- Note: TODO: Check bidi (https://datatracker.ietf.org/doc/html/rfc4518#section-2.5)

ProcessStringDS : ∀ {@0 bs} → DirectoryString bs → String ⊎ Exists─ (List UInt8) Unicode
ProcessStringDS str
  with TranscodeDS str
... | inj₁ err = inj₁ err
... | inj₂ ts
  with InitialMapping (proj₂ ts)
... | ims
  with CaseFoldingNFKC (proj₂ ims)
... | ms
  with Prohibit (proj₂ ms)
... | true = inj₁ "error in stringprep : prohibitted unicode character present"
... | false = inj₂ (InsigCharHandling (proj₂ ms))


CompareDS : ∀ {@0 bs₁ bs₂} → DirectoryString bs₁ → DirectoryString bs₂ → Set
CompareDS x x₁
  with ProcessStringDS x
... | inj₁ err = ⊥
... | inj₂ a
  with ProcessStringDS x₁
... | inj₁ err = ⊥
... | inj₂ b = _≋_ {A = Unicode} (proj₂ a) (proj₂ b)

--------------------------------------------- decidable proofs -------------------------------------------------------

CompareDS-dec : ∀ {@0 bs₁ bs₂} (xs₁ : DirectoryString bs₁) → (xs₂ : DirectoryString bs₂) → Dec (CompareDS xs₁ xs₂)
CompareDS-dec x₁ x₂
  with ProcessStringDS x₁
... | inj₁ err = no (λ ())
... | inj₂ a
  with ProcessStringDS x₂
... | inj₁ err = no (λ ())
--... | inj₂ b = 
... | inj₂ b = _≋?_{A = Unicode} (proj₂ a) (proj₂ b)
