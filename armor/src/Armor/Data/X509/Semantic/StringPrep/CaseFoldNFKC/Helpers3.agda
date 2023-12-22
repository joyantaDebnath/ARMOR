{-# OPTIONS --sized-types #-}

open import Armor.Binary
open import Armor.Prelude
open import Armor.Data.Unicode.UTF8.Serializer
open import Armor.Data.Unicode.UTF8.TCB
open import Armor.Data.Unicode.UTF8.Trie
open import Armor.Data.X509.Semantic.StringPrep.CaseFoldNFKC.M12
open import Armor.Data.X509.Semantic.StringPrep.CaseFoldNFKC.M13
open import Armor.Data.X509.Semantic.StringPrep.CaseFoldNFKC.M141
open import Armor.Data.X509.Semantic.StringPrep.CaseFoldNFKC.M142
import      Armor.Grammar.IList
open import Data.These.Base

module Armor.Data.X509.Semantic.StringPrep.CaseFoldNFKC.Helpers3 where

open Armor.Grammar.IList UInt8

abstract
  B2Map₃ : UTF8Trie
  B2Map₃ = fromList (trie₁₂ ++ trie₁₃ ++ trie₁₄₁ ++ trie₁₄₂)

lookupB2Map₃ : ∀ {@0 bs} → UTF8Char bs → Exists─ (List UInt8) UTF8
lookupB2Map₃ x 
  with lookupUTF8Trie (serializeUTF8Char' x) B2Map₃
... | nothing = _ , (cons (mkIListCons x nil refl))
... | just x₁
  with x₁
... | this x₂ = x₂
... | that x₃ = _ , (cons (mkIListCons x nil refl))
... | these x₂ x₃ = x₂

lookupB2Map₃Flag : ∀ {@0 bs} → UTF8Char bs → Bool
lookupB2Map₃Flag x
  with lookupUTF8Trie (serializeUTF8Char' x) B2Map₃
... | just x₁ = true
... | nothing = false
