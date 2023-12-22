{-# OPTIONS --sized-types #-}

open import Armor.Binary
open import Armor.Prelude
open import Armor.Data.Unicode.UTF8.TCB
open import Armor.Data.Unicode.UTF8.Trie
import      Armor.Grammar.IList

module Armor.Data.X509.Semantic.StringPrep.InitMap.M1 where

open Armor.Grammar.IList UInt8

trie : List (List UInt8 × Exists─ (List UInt8) UTF8)
trie = ((# 9 ∷ []) , (─ ([ # 32 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 32 <? 128 } tt) refl)) nil refl))) ∷ 
  ((# 10 ∷ []) , (─ ([ # 32 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 32 <? 128 } tt) refl)) nil refl))) ∷ 
  ((# 11 ∷ []) , (─ ([ # 32 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 32 <? 128 } tt) refl)) nil refl))) ∷ 
  ((# 12 ∷ []) , (─ ([ # 32 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 32 <? 128 } tt) refl)) nil refl))) ∷ 
  ((# 13 ∷ []) , (─ ([ # 32 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 32 <? 128 } tt) refl)) nil refl))) ∷ 
  ((# 194 ∷ # 160 ∷ []) , (─ ([ # 32 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 32 <? 128 } tt) refl)) nil refl))) ∷ 
  ((# 194 ∷ # 133 ∷ []) , (─ ([ # 32 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 32 <? 128 } tt) refl)) nil refl))) ∷ 
  ((# 225 ∷ # 154 ∷ # 128 ∷ []) , (─ ([ # 32 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 32 <? 128 } tt) refl)) nil refl))) ∷ 
  ((# 226 ∷ # 128 ∷ # 175 ∷ []) , (─ ([ # 32 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 32 <? 128 } tt) refl)) nil refl))) ∷ 
  ((# 226 ∷ # 129 ∷ # 159 ∷ []) , (─ ([ # 32 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 32 <? 128 } tt) refl)) nil refl))) ∷ 
  ((# 226 ∷ # 128 ∷ # 128 ∷ []) , (─ ([ # 32 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 32 <? 128 } tt) refl)) nil refl))) ∷ 
  ((# 226 ∷ # 128 ∷ # 129 ∷ []) , (─ ([ # 32 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 32 <? 128 } tt) refl)) nil refl))) ∷ 
  ((# 226 ∷ # 128 ∷ # 130 ∷ []) , (─ ([ # 32 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 32 <? 128 } tt) refl)) nil refl))) ∷ 
  ((# 226 ∷ # 128 ∷ # 131 ∷ []) , (─ ([ # 32 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 32 <? 128 } tt) refl)) nil refl))) ∷ 
  ((# 226 ∷ # 128 ∷ # 132 ∷ []) , (─ ([ # 32 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 32 <? 128 } tt) refl)) nil refl))) ∷ 
  ((# 226 ∷ # 128 ∷ # 133 ∷ []) , (─ ([ # 32 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 32 <? 128 } tt) refl)) nil refl))) ∷ 
  ((# 226 ∷ # 128 ∷ # 134 ∷ []) , (─ ([ # 32 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 32 <? 128 } tt) refl)) nil refl))) ∷ 
  ((# 226 ∷ # 128 ∷ # 135 ∷ []) , (─ ([ # 32 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 32 <? 128 } tt) refl)) nil refl))) ∷ 
  ((# 226 ∷ # 128 ∷ # 136 ∷ []) , (─ ([ # 32 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 32 <? 128 } tt) refl)) nil refl))) ∷ 
  ((# 226 ∷ # 128 ∷ # 137 ∷ []) , (─ ([ # 32 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 32 <? 128 } tt) refl)) nil refl))) ∷ 
  ((# 226 ∷ # 128 ∷ # 138 ∷ []) , (─ ([ # 32 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 32 <? 128 } tt) refl)) nil refl))) ∷ 
  ((# 226 ∷ # 128 ∷ # 168 ∷ []) , (─ ([ # 32 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 32 <? 128 } tt) refl)) nil refl))) ∷ 
  ((# 226 ∷ # 128 ∷ # 169 ∷ []) , (─ ([ # 32 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 32 <? 128 } tt) refl)) nil refl))) ∷ 
  ((# 227 ∷ # 128 ∷ # 128 ∷ []) , (─ ([ # 32 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 32 <? 128 } tt) refl)) nil refl))) ∷ []


abstract
  IMap : UTF8Trie
  IMap = fromList (trie)
