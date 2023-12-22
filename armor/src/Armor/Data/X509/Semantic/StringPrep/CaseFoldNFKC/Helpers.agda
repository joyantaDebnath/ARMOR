{-# OPTIONS --sized-types #-}

open import Armor.Binary
open import Armor.Prelude
open import Armor.Data.Unicode
open import Armor.Data.Unicode.UTF8.Trie
open import Armor.Data.X509.Semantic.StringPrep.CaseFoldNFKC.Helpers1
open import Armor.Data.X509.Semantic.StringPrep.CaseFoldNFKC.Helpers2
open import Armor.Data.X509.Semantic.StringPrep.CaseFoldNFKC.Helpers3

import      Armor.Grammar.IList
open import Data.These.Base

module Armor.Data.X509.Semantic.StringPrep.CaseFoldNFKC.Helpers where

open Armor.Grammar.IList UInt8

lookupB2Map : ∀ {@0 bs} → UTF8Char bs → Exists─ (List UInt8) UTF8
lookupB2Map x 
  with lookupB2Map₁Flag x
... | true = lookupB2Map₁ x
... | false
  with lookupB2Map₂Flag x
... | true = lookupB2Map₂ x
... | false
  with lookupB2Map₃Flag x
... | true = lookupB2Map₃ x
... | false = _ , (cons (mkIListCons x nil refl))
