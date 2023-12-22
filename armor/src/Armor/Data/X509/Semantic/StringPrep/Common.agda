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
open import Armor.Data.X509.Semantic.StringPrep.CaseFoldNFKC.Helpers
open import Armor.Data.X509.Semantic.StringPrep.InitMap.Helpers
open import Armor.Data.X509.Semantic.StringPrep.InsigCharHandler.Helpers
open import Armor.Data.X509.Semantic.StringPrep.ProhibitList.Helpers

import      Data.Nat.Properties as Nat
open import Data.These.Base

open import Armor.Data.X509.Semantic.StringPrep.ExcludeRange

module Armor.Data.X509.Semantic.StringPrep.Common where

open Armor.Binary
open Armor.Grammar.Definitions UInt8

-- Note: Currently, we only transform unicode strings encoded in UTF8.
-- For UTF16 and UTF32, we do not perform any transformation yet.

appendUTF8 : Exists─ (List UInt8) UTF8 → Exists─ (List UInt8) UTF8 → Exists─ (List UInt8) UTF8
appendUTF8 (fst , snd) (fst₁ , snd₁) = _ , (appendIList _ snd snd₁)

-- https://datatracker.ietf.org/doc/html/rfc4518#section-2.2
InitialMapping : ∀ {@0 bs} → Unicode bs → Exists─ (List UInt8) Unicode
InitialMapping (utf8 nil) = _ , utf8 nil
InitialMapping (utf8 (cons (mkIListCons h t bs≡))) = _ , (utf8 (proj₂ (helper h t)))
  where
  helper : ∀ {@0 bs₁ bs₂} → UTF8Char bs₁ → IList UInt8 UTF8Char bs₂ → Exists─ (List UInt8) UTF8
  helper x nil = case (checkDeleteList x) of λ where
    true → _ , nil
    false → lookupInitMap x
  helper x (cons (mkIListCons head₁ tail₁ bs≡)) = case (checkDeleteList x) of λ where
    true → appendUTF8 (_ , nil) (helper head₁ tail₁)
    false → appendUTF8 (lookupInitMap x) (helper head₁ tail₁)
InitialMapping (utf16 x) = _ , (utf16 x) -- TODO
InitialMapping (utf32 x) = _ , (utf32 x) -- TODO

-- https://datatracker.ietf.org/doc/html/rfc4518#section-2.3
CaseFoldingNFKC : ∀ {@0 bs} → Unicode bs → Exists─ (List UInt8) Unicode
CaseFoldingNFKC (utf8 nil) = _ , utf8 nil
CaseFoldingNFKC (utf8 (cons (mkIListCons h t bs≡))) =  _ , (utf8 (proj₂ (helper h t)))
  where
  helper :  ∀ {@0 bs₁ bs₂} → UTF8Char bs₁ → IList UInt8 UTF8Char bs₂ → Exists─ (List UInt8) UTF8
  helper x nil = lookupB2Map x
  helper x (cons (mkIListCons head₁ tail₁ bs≡)) = appendUTF8 (lookupB2Map x) (helper head₁ tail₁)
CaseFoldingNFKC (utf16 x) = _ , (utf16 x) -- TODO
CaseFoldingNFKC (utf32 x) = _ , (utf32 x) -- TODO

-- https://datatracker.ietf.org/doc/html/rfc4518#section-2.4
Prohibit : ∀ {@0 bs} → Unicode bs → Bool
Prohibit (utf8 nil) = false
Prohibit (utf8 (cons (mkIListCons h t bs≡))) = helper h t
  where
  helper :  ∀ {@0 bs₁ bs₂} → UTF8Char bs₁ → IList UInt8 UTF8Char bs₂ → Bool
  helper x nil = checkProhibitUTF8Char x
  helper x (cons (mkIListCons head₁ tail₁ bs≡)) = case (checkProhibitUTF8Char x) of λ where
    true → true
    false → helper head₁ tail₁
Prohibit (utf16 x) = false -- TODO
Prohibit (utf32 x) = false -- TODO

-- https://datatracker.ietf.org/doc/html/rfc4518#section-2.6
InsigCharHandling : ∀ {@0 bs} → Unicode bs → Exists─ (List UInt8) Unicode
InsigCharHandling (utf8 x)
  with checkOnlySpaces x
  ---- output only two spaces
... | true = _ , (utf8 (appendIList _ (proj₂ spaceUTF8) (proj₂ spaceUTF8)))
  ---- else, ensure one space at start and end, two space per seq of inner spaces
... | false = _ , (utf8 (appendIList _ (appendIList _ (proj₂ spaceUTF8) (proj₂ (innerSeqSpaceHelper (proj₂ (stripUTF8 x)) nil))) (proj₂ spaceUTF8)))
InsigCharHandling (utf16 x) = _ , (utf16 x) -- TODO
InsigCharHandling (utf32 x) = _ , (utf32 x) -- TODO
