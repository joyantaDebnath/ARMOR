{-# OPTIONS --sized-types #-}

open import Data.Nat.DivMod
import      Armor.Binary
open import Armor.Data.X509
import      Armor.Grammar.Definitions
open import Armor.Grammar.IList
import      Armor.Grammar.Sum
open import Armor.Prelude

open import Armor.Data.Unicode
open import Armor.Data.Unicode.UTF8.Trie
open import Armor.Data.X509.Semantic.StringPrep.Common

import      Data.Nat.Properties as Nat
open import Data.These.Base

open import Armor.Data.X509.Semantic.StringPrep.ExcludeRange

module Armor.Data.X509.Semantic.StringPrep.ExecIS where

open Armor.Binary
open Armor.Grammar.Definitions UInt8

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
   
transcodeIS : ∀ {@0 bs} → IA5String bs → Exists─ _ Unicode
transcodeIS (mkTLV len (mkIA5StringValue str all<128) len≡ bs≡) = (-, utf8 (helper (toWitness all<128)))
  where
  helper :  ∀ {bs} → @0 All (Fin._< # 128) bs → UTF8 bs
  helper {[]} x = nil
  helper {x₁ ∷ bs} (px ∷ x) = cons (mkIListCons (utf81 (mkUTF8Char1 x₁ px refl)) (helper x) refl)

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

ProcessStringIS : ∀ {@0 bs} → IA5String bs → String ⊎ Exists─ (List UInt8) Unicode
ProcessStringIS str = do
  let (─ _ , transcoded) = transcodeIS str
  let (─ _ , afterInitMapping) = InitialMapping transcoded
  let (─ _ , afterCaseFold) = CaseFoldingNFKC afterInitMapping
  if (Prohibit afterCaseFold)
    then (inj₁ "StringPrep: ExecIS: prohibited unicode character present")
    else return (InsigCharHandling afterCaseFold)

CompareIS : ∀ {@0 bs₁ bs₂} → IA5String bs₁ → IA5String bs₂ → Set
CompareIS x x₁
  with ProcessStringIS x
... | inj₁ err = ⊥
... | inj₂ a
  with ProcessStringIS x₁
... | inj₁ err = ⊥
... | inj₂ b = _≋_ {A = Unicode} (proj₂ a) (proj₂ b)

--------------------------------------------- decidable proofs -------------------------------------------------------

CompareIS-dec : ∀ {@0 bs₁ bs₂} (xs₁ : IA5String bs₁) → (xs₂ : IA5String bs₂) → Dec (CompareIS xs₁ xs₂)
CompareIS-dec x₁ x₂
  with ProcessStringIS x₁
... | inj₁ err = no (λ ())
... | inj₂ a
  with ProcessStringIS x₂
... | inj₁ err = no (λ ())
--... | inj₂ b = 
... | inj₂ b = _≋?_{A = Unicode} (proj₂ a) (proj₂ b)
