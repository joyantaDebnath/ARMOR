{-# OPTIONS --sized-types #-}

open import Armor.Binary
open import Armor.Prelude
open import Armor.Data.Unicode.UTF8.Serializer
open import Armor.Data.Unicode.UTF8.TCB
open import Armor.Data.Unicode.UTF8.Trie
open import Armor.Data.X509.Semantic.StringPrep.InitMap.M1
open import Armor.Data.X509.Semantic.StringPrep.InitMap.M2
open import Data.These.Base
import      Armor.Grammar.IList

module Armor.Data.X509.Semantic.StringPrep.InitMap.Helpers where

open Armor.Grammar.IList UInt8

lookupInitMap : ∀ {@0 bs} → UTF8Char bs → Exists─ (List UInt8) UTF8
lookupInitMap x 
  with lookupUTF8Trie (serializeUTF8Char' x) IMap
... | nothing = _ , (cons (mkIListCons x nil refl))
... | just x₁
  with x₁
... | this x₂ = x₂
... | that x₃ = _ , (cons (mkIListCons x nil refl))
... | these x₂ x₃ = x₂


checkDeleteList : ∀ {@0 bs} → UTF8Char bs → Bool
checkDeleteList (utf81 x) = DeleteList.CasesForUTF82.check (utf81 x)
checkDeleteList (utf82 x) = DeleteList.CasesForUTF82.check (utf82 x)
checkDeleteList (utf83 x) = DeleteList.CasesForUTF83.check (utf83 x)
checkDeleteList (utf84 x) = DeleteList.CasesForUTF84.check (utf84 x)
