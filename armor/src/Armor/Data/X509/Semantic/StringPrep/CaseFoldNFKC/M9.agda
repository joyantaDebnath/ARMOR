{-# OPTIONS --sized-types --inversion-max-depth=256 #-}

open import Armor.Binary
open import Armor.Prelude
open import Armor.Data.Unicode.UTF8.TCB
open import Armor.Data.Unicode.UTF8.Trie
import      Armor.Grammar.IList

module Armor.Data.X509.Semantic.StringPrep.CaseFoldNFKC.M9 where

open Armor.Grammar.IList UInt8

trie₉ : List (List UInt8 × Exists─ (List UInt8) UTF8)
trie₉ = ((# 227 ∷ # 142 ∷ [ # 128 ]) , (─ (# 112 ∷ [ # 97 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 112 <? 128 } tt) refl)) (cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 97 <? 128 } tt) refl)) nil refl)) refl)))
          ∷ ((# 227 ∷ # 142 ∷ [ # 129 ]) , (─ (# 110 ∷ [ # 97 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 110 <? 128 } tt) refl)) (cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 97 <? 128 } tt) refl)) nil refl)) refl)))
          ∷ ((# 227 ∷ # 142 ∷ [ # 130 ]) , (─ (# 206 ∷ # 188 ∷ [ # 97 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {Q = inRange? 192 223 206 } tt) (toWitness {Q = inRange? 128 191 188 } tt) refl)) (cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 97 <? 128 } tt) refl)) nil refl)) refl)))
          ∷ ((# 227 ∷ # 142 ∷ [ # 131 ]) , (─ (# 109 ∷ [ # 97 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 109 <? 128 } tt) refl)) (cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 97 <? 128 } tt) refl)) nil refl)) refl)))
          ∷ ((# 227 ∷ # 142 ∷ [ # 132 ]) , (─ (# 107 ∷ [ # 97 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 107 <? 128 } tt) refl)) (cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 97 <? 128 } tt) refl)) nil refl)) refl)))
          ∷ ((# 227 ∷ # 142 ∷ [ # 133 ]) , (─ (# 107 ∷ [ # 98 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 107 <? 128 } tt) refl)) (cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 98 <? 128 } tt) refl)) nil refl)) refl)))
          ∷ ((# 227 ∷ # 142 ∷ [ # 134 ]) , (─ (# 109 ∷ [ # 98 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 109 <? 128 } tt) refl)) (cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 98 <? 128 } tt) refl)) nil refl)) refl)))
          ∷ ((# 227 ∷ # 142 ∷ [ # 135 ]) , (─ (# 103 ∷ [ # 98 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 103 <? 128 } tt) refl)) (cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 98 <? 128 } tt) refl)) nil refl)) refl)))
          ∷ ((# 227 ∷ # 142 ∷ [ # 138 ]) , (─ (# 112 ∷ [ # 102 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 112 <? 128 } tt) refl)) (cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 102 <? 128 } tt) refl)) nil refl)) refl)))
          ∷ ((# 227 ∷ # 142 ∷ [ # 139 ]) , (─ (# 110 ∷ [ # 102 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 110 <? 128 } tt) refl)) (cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 102 <? 128 } tt) refl)) nil refl)) refl)))
          ∷ ((# 227 ∷ # 142 ∷ [ # 140 ]) , (─ (# 206 ∷ # 188 ∷ [ # 102 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {Q = inRange? 192 223 206 } tt) (toWitness {Q = inRange? 128 191 188 } tt) refl)) (cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 102 <? 128 } tt) refl)) nil refl)) refl)))
          ∷ ((# 227 ∷ # 142 ∷ [ # 144 ]) , (─ (# 104 ∷ [ # 122 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 104 <? 128 } tt) refl)) (cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 122 <? 128 } tt) refl)) nil refl)) refl)))
          ∷ ((# 227 ∷ # 142 ∷ [ # 145 ]) , (─ (# 107 ∷ # 104 ∷ [ # 122 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 107 <? 128 } tt) refl)) (cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 104 <? 128 } tt) refl)) (cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 122 <? 128 } tt) refl)) nil refl)) refl)) refl)))
          ∷ ((# 227 ∷ # 142 ∷ [ # 146 ]) , (─ (# 109 ∷ # 104 ∷ [ # 122 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 109 <? 128 } tt) refl)) (cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 104 <? 128 } tt) refl)) (cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 122 <? 128 } tt) refl)) nil refl)) refl)) refl)))
          ∷ ((# 227 ∷ # 142 ∷ [ # 147 ]) , (─ (# 103 ∷ # 104 ∷ [ # 122 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 103 <? 128 } tt) refl)) (cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 104 <? 128 } tt) refl)) (cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 122 <? 128 } tt) refl)) nil refl)) refl)) refl)))
          ∷ ((# 227 ∷ # 142 ∷ [ # 148 ]) , (─ (# 116 ∷ # 104 ∷ [ # 122 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 116 <? 128 } tt) refl)) (cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 104 <? 128 } tt) refl)) (cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 122 <? 128 } tt) refl)) nil refl)) refl)) refl)))
          ∷ ((# 227 ∷ # 142 ∷ [ # 169 ]) , (─ (# 112 ∷ [ # 97 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 112 <? 128 } tt) refl)) (cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 97 <? 128 } tt) refl)) nil refl)) refl)))
          ∷ ((# 227 ∷ # 142 ∷ [ # 170 ]) , (─ (# 107 ∷ # 112 ∷ [ # 97 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 107 <? 128 } tt) refl)) (cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 112 <? 128 } tt) refl)) (cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 97 <? 128 } tt) refl)) nil refl)) refl)) refl)))
          ∷ ((# 227 ∷ # 142 ∷ [ # 171 ]) , (─ (# 109 ∷ # 112 ∷ [ # 97 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 109 <? 128 } tt) refl)) (cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 112 <? 128 } tt) refl)) (cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 97 <? 128 } tt) refl)) nil refl)) refl)) refl)))
          ∷ ((# 227 ∷ # 142 ∷ [ # 172 ]) , (─ (# 103 ∷ # 112 ∷ [ # 97 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 103 <? 128 } tt) refl)) (cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 112 <? 128 } tt) refl)) (cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 97 <? 128 } tt) refl)) nil refl)) refl)) refl)))
          ∷ ((# 227 ∷ # 142 ∷ [ # 180 ]) , (─ (# 112 ∷ [ # 118 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 112 <? 128 } tt) refl)) (cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 118 <? 128 } tt) refl)) nil refl)) refl)))
          ∷ ((# 227 ∷ # 142 ∷ [ # 181 ]) , (─ (# 110 ∷ [ # 118 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 110 <? 128 } tt) refl)) (cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 118 <? 128 } tt) refl)) nil refl)) refl)))
          ∷ ((# 227 ∷ # 142 ∷ [ # 182 ]) , (─ (# 206 ∷ # 188 ∷ [ # 118 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {Q = inRange? 192 223 206 } tt) (toWitness {Q = inRange? 128 191 188 } tt) refl)) (cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 118 <? 128 } tt) refl)) nil refl)) refl)))
          ∷ ((# 227 ∷ # 142 ∷ [ # 183 ]) , (─ (# 109 ∷ [ # 118 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 109 <? 128 } tt) refl)) (cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 118 <? 128 } tt) refl)) nil refl)) refl)))
          ∷ ((# 227 ∷ # 142 ∷ [ # 184 ]) , (─ (# 107 ∷ [ # 118 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 107 <? 128 } tt) refl)) (cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 118 <? 128 } tt) refl)) nil refl)) refl)))
          ∷ ((# 227 ∷ # 142 ∷ [ # 185 ]) , (─ (# 109 ∷ [ # 118 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 109 <? 128 } tt) refl)) (cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 118 <? 128 } tt) refl)) nil refl)) refl)))
          ∷ ((# 227 ∷ # 142 ∷ [ # 186 ]) , (─ (# 112 ∷ [ # 119 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 112 <? 128 } tt) refl)) (cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 119 <? 128 } tt) refl)) nil refl)) refl)))
          ∷ ((# 227 ∷ # 142 ∷ [ # 187 ]) , (─ (# 110 ∷ [ # 119 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 110 <? 128 } tt) refl)) (cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 119 <? 128 } tt) refl)) nil refl)) refl)))
          ∷ ((# 227 ∷ # 142 ∷ [ # 188 ]) , (─ (# 206 ∷ # 188 ∷ [ # 119 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {Q = inRange? 192 223 206 } tt) (toWitness {Q = inRange? 128 191 188 } tt) refl)) (cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 119 <? 128 } tt) refl)) nil refl)) refl)))
          ∷ ((# 227 ∷ # 142 ∷ [ # 189 ]) , (─ (# 109 ∷ [ # 119 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 109 <? 128 } tt) refl)) (cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 119 <? 128 } tt) refl)) nil refl)) refl)))
          ∷ ((# 227 ∷ # 142 ∷ [ # 190 ]) , (─ (# 107 ∷ [ # 119 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 107 <? 128 } tt) refl)) (cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 119 <? 128 } tt) refl)) nil refl)) refl)))
          ∷ ((# 227 ∷ # 142 ∷ [ # 191 ]) , (─ (# 109 ∷ [ # 119 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 109 <? 128 } tt) refl)) (cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 119 <? 128 } tt) refl)) nil refl)) refl)))
          ∷ ((# 227 ∷ # 143 ∷ [ # 128 ]) , (─ (# 107 ∷ # 207 ∷ [ # 137 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 107 <? 128 } tt) refl)) (cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {Q = inRange? 192 223 207 } tt) (toWitness {Q = inRange? 128 191 137 } tt) refl)) nil refl)) refl)))
          ∷ ((# 227 ∷ # 143 ∷ [ # 129 ]) , (─ (# 109 ∷ # 207 ∷ [ # 137 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 109 <? 128 } tt) refl)) (cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {Q = inRange? 192 223 207 } tt) (toWitness {Q = inRange? 128 191 137 } tt) refl)) nil refl)) refl)))
          ∷ ((# 227 ∷ # 143 ∷ [ # 131 ]) , (─ (# 98 ∷ [ # 113 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 98 <? 128 } tt) refl)) (cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 113 <? 128 } tt) refl)) nil refl)) refl)))
          ∷ ((# 227 ∷ # 143 ∷ [ # 134 ]) , (─ (# 99 ∷ # 226 ∷ # 136 ∷ # 149 ∷ # 107 ∷ [ # 103 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 99 <? 128 } tt) refl)) (cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 226 } tt) (toWitness {Q = inRange? 128 191 136 } tt) (toWitness {Q = inRange? 128 191 149 } tt) refl)) (cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 107 <? 128 } tt) refl)) (cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 103 <? 128 } tt) refl)) nil refl)) refl)) refl)) refl)))
          ∷ ((# 227 ∷ # 143 ∷ [ # 135 ]) , (─ (# 99 ∷ # 111 ∷ [ # 46 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 99 <? 128 } tt) refl)) (cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 111 <? 128 } tt) refl)) (cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 46 <? 128 } tt) refl)) nil refl)) refl)) refl)))
          ∷ ((# 227 ∷ # 143 ∷ [ # 136 ]) , (─ (# 100 ∷ [ # 98 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 100 <? 128 } tt) refl)) (cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 98 <? 128 } tt) refl)) nil refl)) refl)))
          ∷ ((# 227 ∷ # 143 ∷ [ # 137 ]) , (─ (# 103 ∷ [ # 121 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 103 <? 128 } tt) refl)) (cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 121 <? 128 } tt) refl)) nil refl)) refl)))
          ∷ ((# 227 ∷ # 143 ∷ [ # 139 ]) , (─ (# 104 ∷ [ # 112 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 104 <? 128 } tt) refl)) (cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 112 <? 128 } tt) refl)) nil refl)) refl)))
          ∷ ((# 227 ∷ # 143 ∷ [ # 141 ]) , (─ (# 107 ∷ [ # 107 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 107 <? 128 } tt) refl)) (cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 107 <? 128 } tt) refl)) nil refl)) refl)))
          ∷ ((# 227 ∷ # 143 ∷ [ # 142 ]) , (─ (# 107 ∷ [ # 109 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 107 <? 128 } tt) refl)) (cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 109 <? 128 } tt) refl)) nil refl)) refl)))
          ∷ ((# 227 ∷ # 143 ∷ [ # 151 ]) , (─ (# 112 ∷ [ # 104 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 112 <? 128 } tt) refl)) (cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 104 <? 128 } tt) refl)) nil refl)) refl)))
          ∷ ((# 227 ∷ # 143 ∷ [ # 153 ]) , (─ (# 112 ∷ # 112 ∷ [ # 109 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 112 <? 128 } tt) refl)) (cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 112 <? 128 } tt) refl)) (cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 109 <? 128 } tt) refl)) nil refl)) refl)) refl)))
          ∷ ((# 227 ∷ # 143 ∷ [ # 154 ]) , (─ (# 112 ∷ [ # 114 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 112 <? 128 } tt) refl)) (cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 114 <? 128 } tt) refl)) nil refl)) refl)))
          ∷ ((# 227 ∷ # 143 ∷ [ # 156 ]) , (─ (# 115 ∷ [ # 118 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 115 <? 128 } tt) refl)) (cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 118 <? 128 } tt) refl)) nil refl)) refl)))
          ∷ ((# 227 ∷ # 143 ∷ [ # 157 ]) , (─ (# 119 ∷ [ # 98 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 119 <? 128 } tt) refl)) (cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 98 <? 128 } tt) refl)) nil refl)) refl)))
          ∷ ((# 239 ∷ # 172 ∷ [ # 128 ]) , (─ (# 102 ∷ [ # 102 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 102 <? 128 } tt) refl)) (cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 102 <? 128 } tt) refl)) nil refl)) refl)))
          ∷ ((# 239 ∷ # 172 ∷ [ # 129 ]) , (─ (# 102 ∷ [ # 105 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 102 <? 128 } tt) refl)) (cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 105 <? 128 } tt) refl)) nil refl)) refl)))
          ∷ ((# 239 ∷ # 172 ∷ [ # 130 ]) , (─ (# 102 ∷ [ # 108 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 102 <? 128 } tt) refl)) (cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 108 <? 128 } tt) refl)) nil refl)) refl)))
          ∷ ((# 239 ∷ # 172 ∷ [ # 131 ]) , (─ (# 102 ∷ # 102 ∷ [ # 105 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 102 <? 128 } tt) refl)) (cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 102 <? 128 } tt) refl)) (cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 105 <? 128 } tt) refl)) nil refl)) refl)) refl)))
          ∷ ((# 239 ∷ # 172 ∷ [ # 132 ]) , (─ (# 102 ∷ # 102 ∷ [ # 108 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 102 <? 128 } tt) refl)) (cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 102 <? 128 } tt) refl)) (cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 108 <? 128 } tt) refl)) nil refl)) refl)) refl)))
          ∷ ((# 239 ∷ # 172 ∷ [ # 133 ]) , (─ (# 115 ∷ [ # 116 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 115 <? 128 } tt) refl)) (cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 116 <? 128 } tt) refl)) nil refl)) refl)))
          ∷ ((# 239 ∷ # 172 ∷ [ # 134 ]) , (─ (# 115 ∷ [ # 116 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 115 <? 128 } tt) refl)) (cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 116 <? 128 } tt) refl)) nil refl)) refl)))
          ∷ ((# 239 ∷ # 172 ∷ [ # 147 ]) , (─ (# 213 ∷ # 180 ∷ # 213 ∷ [ # 182 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {Q = inRange? 192 223 213 } tt) (toWitness {Q = inRange? 128 191 180 } tt) refl)) (cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {Q = inRange? 192 223 213 } tt) (toWitness {Q = inRange? 128 191 182 } tt) refl)) nil refl)) refl)))
          ∷ ((# 239 ∷ # 172 ∷ [ # 148 ]) , (─ (# 213 ∷ # 180 ∷ # 213 ∷ [ # 165 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {Q = inRange? 192 223 213 } tt) (toWitness {Q = inRange? 128 191 180 } tt) refl)) (cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {Q = inRange? 192 223 213 } tt) (toWitness {Q = inRange? 128 191 165 } tt) refl)) nil refl)) refl)))
          ∷ ((# 239 ∷ # 172 ∷ [ # 149 ]) , (─ (# 213 ∷ # 180 ∷ # 213 ∷ [ # 171 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {Q = inRange? 192 223 213 } tt) (toWitness {Q = inRange? 128 191 180 } tt) refl)) (cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {Q = inRange? 192 223 213 } tt) (toWitness {Q = inRange? 128 191 171 } tt) refl)) nil refl)) refl)))
          ∷ ((# 239 ∷ # 172 ∷ [ # 150 ]) , (─ (# 213 ∷ # 190 ∷ # 213 ∷ [ # 182 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {Q = inRange? 192 223 213 } tt) (toWitness {Q = inRange? 128 191 190 } tt) refl)) (cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {Q = inRange? 192 223 213 } tt) (toWitness {Q = inRange? 128 191 182 } tt) refl)) nil refl)) refl)))
          ∷ ((# 239 ∷ # 172 ∷ [ # 151 ]) , (─ (# 213 ∷ # 180 ∷ # 213 ∷ [ # 173 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {Q = inRange? 192 223 213 } tt) (toWitness {Q = inRange? 128 191 180 } tt) refl)) (cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {Q = inRange? 192 223 213 } tt) (toWitness {Q = inRange? 128 191 173 } tt) refl)) nil refl)) refl)))
          ∷ ((# 239 ∷ # 188 ∷ [ # 161 ]) , (─ (# 239 ∷ # 189 ∷ [ # 129 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 239 } tt) (toWitness {Q = inRange? 128 191 189 } tt) (toWitness {Q = inRange? 128 191 129 } tt) refl)) nil refl)))
          ∷ ((# 239 ∷ # 188 ∷ [ # 162 ]) , (─ (# 239 ∷ # 189 ∷ [ # 130 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 239 } tt) (toWitness {Q = inRange? 128 191 189 } tt) (toWitness {Q = inRange? 128 191 130 } tt) refl)) nil refl)))
          ∷ ((# 239 ∷ # 188 ∷ [ # 163 ]) , (─ (# 239 ∷ # 189 ∷ [ # 131 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 239 } tt) (toWitness {Q = inRange? 128 191 189 } tt) (toWitness {Q = inRange? 128 191 131 } tt) refl)) nil refl)))
          ∷ ((# 239 ∷ # 188 ∷ [ # 164 ]) , (─ (# 239 ∷ # 189 ∷ [ # 132 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 239 } tt) (toWitness {Q = inRange? 128 191 189 } tt) (toWitness {Q = inRange? 128 191 132 } tt) refl)) nil refl)))
          ∷ ((# 239 ∷ # 188 ∷ [ # 165 ]) , (─ (# 239 ∷ # 189 ∷ [ # 133 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 239 } tt) (toWitness {Q = inRange? 128 191 189 } tt) (toWitness {Q = inRange? 128 191 133 } tt) refl)) nil refl)))
          ∷ ((# 239 ∷ # 188 ∷ [ # 166 ]) , (─ (# 239 ∷ # 189 ∷ [ # 134 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 239 } tt) (toWitness {Q = inRange? 128 191 189 } tt) (toWitness {Q = inRange? 128 191 134 } tt) refl)) nil refl)))
          ∷ ((# 239 ∷ # 188 ∷ [ # 167 ]) , (─ (# 239 ∷ # 189 ∷ [ # 135 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 239 } tt) (toWitness {Q = inRange? 128 191 189 } tt) (toWitness {Q = inRange? 128 191 135 } tt) refl)) nil refl)))
          ∷ ((# 239 ∷ # 188 ∷ [ # 168 ]) , (─ (# 239 ∷ # 189 ∷ [ # 136 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 239 } tt) (toWitness {Q = inRange? 128 191 189 } tt) (toWitness {Q = inRange? 128 191 136 } tt) refl)) nil refl)))
          ∷ ((# 239 ∷ # 188 ∷ [ # 169 ]) , (─ (# 239 ∷ # 189 ∷ [ # 137 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 239 } tt) (toWitness {Q = inRange? 128 191 189 } tt) (toWitness {Q = inRange? 128 191 137 } tt) refl)) nil refl)))
          ∷ ((# 239 ∷ # 188 ∷ [ # 170 ]) , (─ (# 239 ∷ # 189 ∷ [ # 138 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 239 } tt) (toWitness {Q = inRange? 128 191 189 } tt) (toWitness {Q = inRange? 128 191 138 } tt) refl)) nil refl)))
          ∷ ((# 239 ∷ # 188 ∷ [ # 171 ]) , (─ (# 239 ∷ # 189 ∷ [ # 139 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 239 } tt) (toWitness {Q = inRange? 128 191 189 } tt) (toWitness {Q = inRange? 128 191 139 } tt) refl)) nil refl)))
          ∷ ((# 239 ∷ # 188 ∷ [ # 172 ]) , (─ (# 239 ∷ # 189 ∷ [ # 140 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 239 } tt) (toWitness {Q = inRange? 128 191 189 } tt) (toWitness {Q = inRange? 128 191 140 } tt) refl)) nil refl)))
          ∷ ((# 239 ∷ # 188 ∷ [ # 173 ]) , (─ (# 239 ∷ # 189 ∷ [ # 141 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 239 } tt) (toWitness {Q = inRange? 128 191 189 } tt) (toWitness {Q = inRange? 128 191 141 } tt) refl)) nil refl)))
          ∷ ((# 239 ∷ # 188 ∷ [ # 174 ]) , (─ (# 239 ∷ # 189 ∷ [ # 142 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 239 } tt) (toWitness {Q = inRange? 128 191 189 } tt) (toWitness {Q = inRange? 128 191 142 } tt) refl)) nil refl)))
          ∷ ((# 239 ∷ # 188 ∷ [ # 175 ]) , (─ (# 239 ∷ # 189 ∷ [ # 143 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 239 } tt) (toWitness {Q = inRange? 128 191 189 } tt) (toWitness {Q = inRange? 128 191 143 } tt) refl)) nil refl)))
          ∷ ((# 239 ∷ # 188 ∷ [ # 176 ]) , (─ (# 239 ∷ # 189 ∷ [ # 144 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 239 } tt) (toWitness {Q = inRange? 128 191 189 } tt) (toWitness {Q = inRange? 128 191 144 } tt) refl)) nil refl)))
          ∷ ((# 239 ∷ # 188 ∷ [ # 177 ]) , (─ (# 239 ∷ # 189 ∷ [ # 145 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 239 } tt) (toWitness {Q = inRange? 128 191 189 } tt) (toWitness {Q = inRange? 128 191 145 } tt) refl)) nil refl)))
          ∷ ((# 239 ∷ # 188 ∷ [ # 178 ]) , (─ (# 239 ∷ # 189 ∷ [ # 146 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 239 } tt) (toWitness {Q = inRange? 128 191 189 } tt) (toWitness {Q = inRange? 128 191 146 } tt) refl)) nil refl)))
          ∷ ((# 239 ∷ # 188 ∷ [ # 179 ]) , (─ (# 239 ∷ # 189 ∷ [ # 147 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 239 } tt) (toWitness {Q = inRange? 128 191 189 } tt) (toWitness {Q = inRange? 128 191 147 } tt) refl)) nil refl)))
          ∷ ((# 239 ∷ # 188 ∷ [ # 180 ]) , (─ (# 239 ∷ # 189 ∷ [ # 148 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 239 } tt) (toWitness {Q = inRange? 128 191 189 } tt) (toWitness {Q = inRange? 128 191 148 } tt) refl)) nil refl)))
          ∷ ((# 239 ∷ # 188 ∷ [ # 181 ]) , (─ (# 239 ∷ # 189 ∷ [ # 149 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 239 } tt) (toWitness {Q = inRange? 128 191 189 } tt) (toWitness {Q = inRange? 128 191 149 } tt) refl)) nil refl)))
          ∷ ((# 239 ∷ # 188 ∷ [ # 182 ]) , (─ (# 239 ∷ # 189 ∷ [ # 150 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 239 } tt) (toWitness {Q = inRange? 128 191 189 } tt) (toWitness {Q = inRange? 128 191 150 } tt) refl)) nil refl)))
          ∷ ((# 239 ∷ # 188 ∷ [ # 183 ]) , (─ (# 239 ∷ # 189 ∷ [ # 151 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 239 } tt) (toWitness {Q = inRange? 128 191 189 } tt) (toWitness {Q = inRange? 128 191 151 } tt) refl)) nil refl)))
          ∷ ((# 239 ∷ # 188 ∷ [ # 184 ]) , (─ (# 239 ∷ # 189 ∷ [ # 152 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 239 } tt) (toWitness {Q = inRange? 128 191 189 } tt) (toWitness {Q = inRange? 128 191 152 } tt) refl)) nil refl)))
          ∷ ((# 239 ∷ # 188 ∷ [ # 185 ]) , (─ (# 239 ∷ # 189 ∷ [ # 153 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 239 } tt) (toWitness {Q = inRange? 128 191 189 } tt) (toWitness {Q = inRange? 128 191 153 } tt) refl)) nil refl)))
          ∷ ((# 239 ∷ # 188 ∷ [ # 186 ]) , (─ (# 239 ∷ # 189 ∷ [ # 154 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 239 } tt) (toWitness {Q = inRange? 128 191 189 } tt) (toWitness {Q = inRange? 128 191 154 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 144 ∷ # 144 ∷ [ # 128 ]) , (─ (# 240 ∷ # 144 ∷ # 144 ∷ [ # 168 ]) , cons (mkIListCons (utf84 (mkUTF8Char4 _ _ _ _ (toWitness {Q = inRange? 240 247 240 } tt) (toWitness {Q = inRange? 128 191 144 } tt) (toWitness {Q = inRange? 128 191 144 } tt) (toWitness {Q = inRange? 128 191 168 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 144 ∷ # 144 ∷ [ # 129 ]) , (─ (# 240 ∷ # 144 ∷ # 144 ∷ [ # 169 ]) , cons (mkIListCons (utf84 (mkUTF8Char4 _ _ _ _ (toWitness {Q = inRange? 240 247 240 } tt) (toWitness {Q = inRange? 128 191 144 } tt) (toWitness {Q = inRange? 128 191 144 } tt) (toWitness {Q = inRange? 128 191 169 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 144 ∷ # 144 ∷ [ # 130 ]) , (─ (# 240 ∷ # 144 ∷ # 144 ∷ [ # 170 ]) , cons (mkIListCons (utf84 (mkUTF8Char4 _ _ _ _ (toWitness {Q = inRange? 240 247 240 } tt) (toWitness {Q = inRange? 128 191 144 } tt) (toWitness {Q = inRange? 128 191 144 } tt) (toWitness {Q = inRange? 128 191 170 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 144 ∷ # 144 ∷ [ # 131 ]) , (─ (# 240 ∷ # 144 ∷ # 144 ∷ [ # 171 ]) , cons (mkIListCons (utf84 (mkUTF8Char4 _ _ _ _ (toWitness {Q = inRange? 240 247 240 } tt) (toWitness {Q = inRange? 128 191 144 } tt) (toWitness {Q = inRange? 128 191 144 } tt) (toWitness {Q = inRange? 128 191 171 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 144 ∷ # 144 ∷ [ # 132 ]) , (─ (# 240 ∷ # 144 ∷ # 144 ∷ [ # 172 ]) , cons (mkIListCons (utf84 (mkUTF8Char4 _ _ _ _ (toWitness {Q = inRange? 240 247 240 } tt) (toWitness {Q = inRange? 128 191 144 } tt) (toWitness {Q = inRange? 128 191 144 } tt) (toWitness {Q = inRange? 128 191 172 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 144 ∷ # 144 ∷ [ # 133 ]) , (─ (# 240 ∷ # 144 ∷ # 144 ∷ [ # 173 ]) , cons (mkIListCons (utf84 (mkUTF8Char4 _ _ _ _ (toWitness {Q = inRange? 240 247 240 } tt) (toWitness {Q = inRange? 128 191 144 } tt) (toWitness {Q = inRange? 128 191 144 } tt) (toWitness {Q = inRange? 128 191 173 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 144 ∷ # 144 ∷ [ # 134 ]) , (─ (# 240 ∷ # 144 ∷ # 144 ∷ [ # 174 ]) , cons (mkIListCons (utf84 (mkUTF8Char4 _ _ _ _ (toWitness {Q = inRange? 240 247 240 } tt) (toWitness {Q = inRange? 128 191 144 } tt) (toWitness {Q = inRange? 128 191 144 } tt) (toWitness {Q = inRange? 128 191 174 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 144 ∷ # 144 ∷ [ # 135 ]) , (─ (# 240 ∷ # 144 ∷ # 144 ∷ [ # 175 ]) , cons (mkIListCons (utf84 (mkUTF8Char4 _ _ _ _ (toWitness {Q = inRange? 240 247 240 } tt) (toWitness {Q = inRange? 128 191 144 } tt) (toWitness {Q = inRange? 128 191 144 } tt) (toWitness {Q = inRange? 128 191 175 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 144 ∷ # 144 ∷ [ # 136 ]) , (─ (# 240 ∷ # 144 ∷ # 144 ∷ [ # 176 ]) , cons (mkIListCons (utf84 (mkUTF8Char4 _ _ _ _ (toWitness {Q = inRange? 240 247 240 } tt) (toWitness {Q = inRange? 128 191 144 } tt) (toWitness {Q = inRange? 128 191 144 } tt) (toWitness {Q = inRange? 128 191 176 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 144 ∷ # 144 ∷ [ # 137 ]) , (─ (# 240 ∷ # 144 ∷ # 144 ∷ [ # 177 ]) , cons (mkIListCons (utf84 (mkUTF8Char4 _ _ _ _ (toWitness {Q = inRange? 240 247 240 } tt) (toWitness {Q = inRange? 128 191 144 } tt) (toWitness {Q = inRange? 128 191 144 } tt) (toWitness {Q = inRange? 128 191 177 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 144 ∷ # 144 ∷ [ # 138 ]) , (─ (# 240 ∷ # 144 ∷ # 144 ∷ [ # 178 ]) , cons (mkIListCons (utf84 (mkUTF8Char4 _ _ _ _ (toWitness {Q = inRange? 240 247 240 } tt) (toWitness {Q = inRange? 128 191 144 } tt) (toWitness {Q = inRange? 128 191 144 } tt) (toWitness {Q = inRange? 128 191 178 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 144 ∷ # 144 ∷ [ # 139 ]) , (─ (# 240 ∷ # 144 ∷ # 144 ∷ [ # 179 ]) , cons (mkIListCons (utf84 (mkUTF8Char4 _ _ _ _ (toWitness {Q = inRange? 240 247 240 } tt) (toWitness {Q = inRange? 128 191 144 } tt) (toWitness {Q = inRange? 128 191 144 } tt) (toWitness {Q = inRange? 128 191 179 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 144 ∷ # 144 ∷ [ # 140 ]) , (─ (# 240 ∷ # 144 ∷ # 144 ∷ [ # 180 ]) , cons (mkIListCons (utf84 (mkUTF8Char4 _ _ _ _ (toWitness {Q = inRange? 240 247 240 } tt) (toWitness {Q = inRange? 128 191 144 } tt) (toWitness {Q = inRange? 128 191 144 } tt) (toWitness {Q = inRange? 128 191 180 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 144 ∷ # 144 ∷ [ # 141 ]) , (─ (# 240 ∷ # 144 ∷ # 144 ∷ [ # 181 ]) , cons (mkIListCons (utf84 (mkUTF8Char4 _ _ _ _ (toWitness {Q = inRange? 240 247 240 } tt) (toWitness {Q = inRange? 128 191 144 } tt) (toWitness {Q = inRange? 128 191 144 } tt) (toWitness {Q = inRange? 128 191 181 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 144 ∷ # 144 ∷ [ # 142 ]) , (─ (# 240 ∷ # 144 ∷ # 144 ∷ [ # 182 ]) , cons (mkIListCons (utf84 (mkUTF8Char4 _ _ _ _ (toWitness {Q = inRange? 240 247 240 } tt) (toWitness {Q = inRange? 128 191 144 } tt) (toWitness {Q = inRange? 128 191 144 } tt) (toWitness {Q = inRange? 128 191 182 } tt) refl)) nil refl)))
          ∷ []


