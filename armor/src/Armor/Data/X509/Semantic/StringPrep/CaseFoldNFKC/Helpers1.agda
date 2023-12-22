
{-# OPTIONS --sized-types #-}

open import Armor.Binary
open import Armor.Prelude
open import Armor.Data.Unicode.UTF8.Serializer
open import Armor.Data.Unicode.UTF8.TCB
open import Armor.Data.Unicode.UTF8.Trie
open import Armor.Data.X509.Semantic.StringPrep.CaseFoldNFKC.M1
open import Armor.Data.X509.Semantic.StringPrep.CaseFoldNFKC.M2
open import Armor.Data.X509.Semantic.StringPrep.CaseFoldNFKC.M3
open import Armor.Data.X509.Semantic.StringPrep.CaseFoldNFKC.M4
open import Armor.Data.X509.Semantic.StringPrep.CaseFoldNFKC.M5
open import Armor.Data.X509.Semantic.StringPrep.CaseFoldNFKC.M6

import      Armor.Grammar.IList
open import Data.These.Base

module Armor.Data.X509.Semantic.StringPrep.CaseFoldNFKC.Helpers1 where

open Armor.Grammar.IList UInt8

abstract
  B2Map₁ : UTF8Trie
  B2Map₁ = fromList (trie₁ ++ trie₂ ++ trie₃ ++ trie₄ ++ trie₅ ++ trie₆)

lookupB2Map₁ : ∀ {@0 bs} → UTF8Char bs → Exists─ (List UInt8) UTF8
lookupB2Map₁ x 
  with lookupUTF8Trie (serializeUTF8Char' x) B2Map₁
... | nothing = _ , (cons (mkIListCons x nil refl))
... | just x₁
  with x₁
... | this x₂ = x₂
... | that x₃ = _ , (cons (mkIListCons x nil refl))
... | these x₂ x₃ = x₂

lookupB2Map₁Flag : ∀ {@0 bs} → UTF8Char bs → Bool
lookupB2Map₁Flag x
  with lookupUTF8Trie (serializeUTF8Char' x) B2Map₁
... | just x₁ = true
... | nothing = false
