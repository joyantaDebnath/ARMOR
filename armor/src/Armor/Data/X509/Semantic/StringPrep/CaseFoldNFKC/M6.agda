{-# OPTIONS --sized-types #-}

open import Armor.Binary
open import Armor.Prelude
open import Armor.Data.Unicode.UTF8.TCB
open import Armor.Data.Unicode.UTF8.Trie
import      Armor.Grammar.IList

module Armor.Data.X509.Semantic.StringPrep.CaseFoldNFKC.M6 where

open Armor.Grammar.IList UInt8

trie₆ : List (List UInt8 × Exists─ (List UInt8) UTF8)
trie₆ = ((# 225 ∷ # 185 ∷ [ # 172 ]) , (─ (# 225 ∷ # 185 ∷ [ # 173 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 185 } tt) (toWitness {Q = inRange? 128 191 173 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 185 ∷ [ # 174 ]) , (─ (# 225 ∷ # 185 ∷ [ # 175 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 185 } tt) (toWitness {Q = inRange? 128 191 175 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 185 ∷ [ # 176 ]) , (─ (# 225 ∷ # 185 ∷ [ # 177 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 185 } tt) (toWitness {Q = inRange? 128 191 177 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 185 ∷ [ # 178 ]) , (─ (# 225 ∷ # 185 ∷ [ # 179 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 185 } tt) (toWitness {Q = inRange? 128 191 179 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 185 ∷ [ # 180 ]) , (─ (# 225 ∷ # 185 ∷ [ # 181 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 185 } tt) (toWitness {Q = inRange? 128 191 181 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 185 ∷ [ # 182 ]) , (─ (# 225 ∷ # 185 ∷ [ # 183 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 185 } tt) (toWitness {Q = inRange? 128 191 183 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 185 ∷ [ # 184 ]) , (─ (# 225 ∷ # 185 ∷ [ # 185 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 185 } tt) (toWitness {Q = inRange? 128 191 185 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 185 ∷ [ # 186 ]) , (─ (# 225 ∷ # 185 ∷ [ # 187 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 185 } tt) (toWitness {Q = inRange? 128 191 187 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 185 ∷ [ # 188 ]) , (─ (# 225 ∷ # 185 ∷ [ # 189 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 185 } tt) (toWitness {Q = inRange? 128 191 189 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 185 ∷ [ # 190 ]) , (─ (# 225 ∷ # 185 ∷ [ # 191 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 185 } tt) (toWitness {Q = inRange? 128 191 191 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 186 ∷ [ # 128 ]) , (─ (# 225 ∷ # 186 ∷ [ # 129 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 186 } tt) (toWitness {Q = inRange? 128 191 129 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 186 ∷ [ # 130 ]) , (─ (# 225 ∷ # 186 ∷ [ # 131 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 186 } tt) (toWitness {Q = inRange? 128 191 131 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 186 ∷ [ # 132 ]) , (─ (# 225 ∷ # 186 ∷ [ # 133 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 186 } tt) (toWitness {Q = inRange? 128 191 133 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 186 ∷ [ # 134 ]) , (─ (# 225 ∷ # 186 ∷ [ # 135 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 186 } tt) (toWitness {Q = inRange? 128 191 135 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 186 ∷ [ # 136 ]) , (─ (# 225 ∷ # 186 ∷ [ # 137 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 186 } tt) (toWitness {Q = inRange? 128 191 137 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 186 ∷ [ # 138 ]) , (─ (# 225 ∷ # 186 ∷ [ # 139 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 186 } tt) (toWitness {Q = inRange? 128 191 139 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 186 ∷ [ # 140 ]) , (─ (# 225 ∷ # 186 ∷ [ # 141 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 186 } tt) (toWitness {Q = inRange? 128 191 141 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 186 ∷ [ # 142 ]) , (─ (# 225 ∷ # 186 ∷ [ # 143 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 186 } tt) (toWitness {Q = inRange? 128 191 143 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 186 ∷ [ # 144 ]) , (─ (# 225 ∷ # 186 ∷ [ # 145 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 186 } tt) (toWitness {Q = inRange? 128 191 145 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 186 ∷ [ # 146 ]) , (─ (# 225 ∷ # 186 ∷ [ # 147 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 186 } tt) (toWitness {Q = inRange? 128 191 147 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 186 ∷ [ # 148 ]) , (─ (# 225 ∷ # 186 ∷ [ # 149 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 186 } tt) (toWitness {Q = inRange? 128 191 149 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 186 ∷ [ # 150 ]) , (─ (# 104 ∷ # 204 ∷ [ # 177 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 104 <? 128 } tt) refl)) (cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {Q = inRange? 192 223 204 } tt) (toWitness {Q = inRange? 128 191 177 } tt) refl)) nil refl)) refl)))
          ∷ ((# 225 ∷ # 186 ∷ [ # 151 ]) , (─ (# 116 ∷ # 204 ∷ [ # 136 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 116 <? 128 } tt) refl)) (cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {Q = inRange? 192 223 204 } tt) (toWitness {Q = inRange? 128 191 136 } tt) refl)) nil refl)) refl)))
          ∷ ((# 225 ∷ # 186 ∷ [ # 152 ]) , (─ (# 119 ∷ # 204 ∷ [ # 138 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 119 <? 128 } tt) refl)) (cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {Q = inRange? 192 223 204 } tt) (toWitness {Q = inRange? 128 191 138 } tt) refl)) nil refl)) refl)))
          ∷ ((# 225 ∷ # 186 ∷ [ # 153 ]) , (─ (# 121 ∷ # 204 ∷ [ # 138 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 121 <? 128 } tt) refl)) (cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {Q = inRange? 192 223 204 } tt) (toWitness {Q = inRange? 128 191 138 } tt) refl)) nil refl)) refl)))
          ∷ ((# 225 ∷ # 186 ∷ [ # 154 ]) , (─ (# 97 ∷ # 202 ∷ [ # 190 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 97 <? 128 } tt) refl)) (cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {Q = inRange? 192 223 202 } tt) (toWitness {Q = inRange? 128 191 190 } tt) refl)) nil refl)) refl)))
          ∷ ((# 225 ∷ # 186 ∷ [ # 155 ]) , (─ (# 225 ∷ # 185 ∷ [ # 161 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 185 } tt) (toWitness {Q = inRange? 128 191 161 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 186 ∷ [ # 160 ]) , (─ (# 225 ∷ # 186 ∷ [ # 161 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 186 } tt) (toWitness {Q = inRange? 128 191 161 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 186 ∷ [ # 162 ]) , (─ (# 225 ∷ # 186 ∷ [ # 163 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 186 } tt) (toWitness {Q = inRange? 128 191 163 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 186 ∷ [ # 164 ]) , (─ (# 225 ∷ # 186 ∷ [ # 165 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 186 } tt) (toWitness {Q = inRange? 128 191 165 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 186 ∷ [ # 166 ]) , (─ (# 225 ∷ # 186 ∷ [ # 167 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 186 } tt) (toWitness {Q = inRange? 128 191 167 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 186 ∷ [ # 168 ]) , (─ (# 225 ∷ # 186 ∷ [ # 169 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 186 } tt) (toWitness {Q = inRange? 128 191 169 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 186 ∷ [ # 170 ]) , (─ (# 225 ∷ # 186 ∷ [ # 171 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 186 } tt) (toWitness {Q = inRange? 128 191 171 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 186 ∷ [ # 172 ]) , (─ (# 225 ∷ # 186 ∷ [ # 173 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 186 } tt) (toWitness {Q = inRange? 128 191 173 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 186 ∷ [ # 174 ]) , (─ (# 225 ∷ # 186 ∷ [ # 175 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 186 } tt) (toWitness {Q = inRange? 128 191 175 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 186 ∷ [ # 176 ]) , (─ (# 225 ∷ # 186 ∷ [ # 177 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 186 } tt) (toWitness {Q = inRange? 128 191 177 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 186 ∷ [ # 178 ]) , (─ (# 225 ∷ # 186 ∷ [ # 179 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 186 } tt) (toWitness {Q = inRange? 128 191 179 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 186 ∷ [ # 180 ]) , (─ (# 225 ∷ # 186 ∷ [ # 181 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 186 } tt) (toWitness {Q = inRange? 128 191 181 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 186 ∷ [ # 182 ]) , (─ (# 225 ∷ # 186 ∷ [ # 183 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 186 } tt) (toWitness {Q = inRange? 128 191 183 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 186 ∷ [ # 184 ]) , (─ (# 225 ∷ # 186 ∷ [ # 185 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 186 } tt) (toWitness {Q = inRange? 128 191 185 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 186 ∷ [ # 186 ]) , (─ (# 225 ∷ # 186 ∷ [ # 187 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 186 } tt) (toWitness {Q = inRange? 128 191 187 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 186 ∷ [ # 188 ]) , (─ (# 225 ∷ # 186 ∷ [ # 189 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 186 } tt) (toWitness {Q = inRange? 128 191 189 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 186 ∷ [ # 190 ]) , (─ (# 225 ∷ # 186 ∷ [ # 191 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 186 } tt) (toWitness {Q = inRange? 128 191 191 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 187 ∷ [ # 128 ]) , (─ (# 225 ∷ # 187 ∷ [ # 129 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 187 } tt) (toWitness {Q = inRange? 128 191 129 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 187 ∷ [ # 130 ]) , (─ (# 225 ∷ # 187 ∷ [ # 131 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 187 } tt) (toWitness {Q = inRange? 128 191 131 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 187 ∷ [ # 132 ]) , (─ (# 225 ∷ # 187 ∷ [ # 133 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 187 } tt) (toWitness {Q = inRange? 128 191 133 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 187 ∷ [ # 134 ]) , (─ (# 225 ∷ # 187 ∷ [ # 135 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 187 } tt) (toWitness {Q = inRange? 128 191 135 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 187 ∷ [ # 136 ]) , (─ (# 225 ∷ # 187 ∷ [ # 137 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 187 } tt) (toWitness {Q = inRange? 128 191 137 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 187 ∷ [ # 138 ]) , (─ (# 225 ∷ # 187 ∷ [ # 139 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 187 } tt) (toWitness {Q = inRange? 128 191 139 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 187 ∷ [ # 140 ]) , (─ (# 225 ∷ # 187 ∷ [ # 141 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 187 } tt) (toWitness {Q = inRange? 128 191 141 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 187 ∷ [ # 142 ]) , (─ (# 225 ∷ # 187 ∷ [ # 143 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 187 } tt) (toWitness {Q = inRange? 128 191 143 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 187 ∷ [ # 144 ]) , (─ (# 225 ∷ # 187 ∷ [ # 145 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 187 } tt) (toWitness {Q = inRange? 128 191 145 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 187 ∷ [ # 146 ]) , (─ (# 225 ∷ # 187 ∷ [ # 147 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 187 } tt) (toWitness {Q = inRange? 128 191 147 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 187 ∷ [ # 148 ]) , (─ (# 225 ∷ # 187 ∷ [ # 149 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 187 } tt) (toWitness {Q = inRange? 128 191 149 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 187 ∷ [ # 150 ]) , (─ (# 225 ∷ # 187 ∷ [ # 151 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 187 } tt) (toWitness {Q = inRange? 128 191 151 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 187 ∷ [ # 152 ]) , (─ (# 225 ∷ # 187 ∷ [ # 153 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 187 } tt) (toWitness {Q = inRange? 128 191 153 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 187 ∷ [ # 154 ]) , (─ (# 225 ∷ # 187 ∷ [ # 155 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 187 } tt) (toWitness {Q = inRange? 128 191 155 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 187 ∷ [ # 156 ]) , (─ (# 225 ∷ # 187 ∷ [ # 157 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 187 } tt) (toWitness {Q = inRange? 128 191 157 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 187 ∷ [ # 158 ]) , (─ (# 225 ∷ # 187 ∷ [ # 159 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 187 } tt) (toWitness {Q = inRange? 128 191 159 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 187 ∷ [ # 160 ]) , (─ (# 225 ∷ # 187 ∷ [ # 161 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 187 } tt) (toWitness {Q = inRange? 128 191 161 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 187 ∷ [ # 162 ]) , (─ (# 225 ∷ # 187 ∷ [ # 163 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 187 } tt) (toWitness {Q = inRange? 128 191 163 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 187 ∷ [ # 164 ]) , (─ (# 225 ∷ # 187 ∷ [ # 165 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 187 } tt) (toWitness {Q = inRange? 128 191 165 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 187 ∷ [ # 166 ]) , (─ (# 225 ∷ # 187 ∷ [ # 167 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 187 } tt) (toWitness {Q = inRange? 128 191 167 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 187 ∷ [ # 168 ]) , (─ (# 225 ∷ # 187 ∷ [ # 169 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 187 } tt) (toWitness {Q = inRange? 128 191 169 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 187 ∷ [ # 170 ]) , (─ (# 225 ∷ # 187 ∷ [ # 171 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 187 } tt) (toWitness {Q = inRange? 128 191 171 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 187 ∷ [ # 172 ]) , (─ (# 225 ∷ # 187 ∷ [ # 173 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 187 } tt) (toWitness {Q = inRange? 128 191 173 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 187 ∷ [ # 174 ]) , (─ (# 225 ∷ # 187 ∷ [ # 175 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 187 } tt) (toWitness {Q = inRange? 128 191 175 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 187 ∷ [ # 176 ]) , (─ (# 225 ∷ # 187 ∷ [ # 177 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 187 } tt) (toWitness {Q = inRange? 128 191 177 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 187 ∷ [ # 178 ]) , (─ (# 225 ∷ # 187 ∷ [ # 179 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 187 } tt) (toWitness {Q = inRange? 128 191 179 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 187 ∷ [ # 180 ]) , (─ (# 225 ∷ # 187 ∷ [ # 181 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 187 } tt) (toWitness {Q = inRange? 128 191 181 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 187 ∷ [ # 182 ]) , (─ (# 225 ∷ # 187 ∷ [ # 183 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 187 } tt) (toWitness {Q = inRange? 128 191 183 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 187 ∷ [ # 184 ]) , (─ (# 225 ∷ # 187 ∷ [ # 185 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 187 } tt) (toWitness {Q = inRange? 128 191 185 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 188 ∷ [ # 136 ]) , (─ (# 225 ∷ # 188 ∷ [ # 128 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 188 } tt) (toWitness {Q = inRange? 128 191 128 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 188 ∷ [ # 137 ]) , (─ (# 225 ∷ # 188 ∷ [ # 129 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 188 } tt) (toWitness {Q = inRange? 128 191 129 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 188 ∷ [ # 138 ]) , (─ (# 225 ∷ # 188 ∷ [ # 130 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 188 } tt) (toWitness {Q = inRange? 128 191 130 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 188 ∷ [ # 139 ]) , (─ (# 225 ∷ # 188 ∷ [ # 131 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 188 } tt) (toWitness {Q = inRange? 128 191 131 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 188 ∷ [ # 140 ]) , (─ (# 225 ∷ # 188 ∷ [ # 132 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 188 } tt) (toWitness {Q = inRange? 128 191 132 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 188 ∷ [ # 141 ]) , (─ (# 225 ∷ # 188 ∷ [ # 133 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 188 } tt) (toWitness {Q = inRange? 128 191 133 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 188 ∷ [ # 142 ]) , (─ (# 225 ∷ # 188 ∷ [ # 134 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 188 } tt) (toWitness {Q = inRange? 128 191 134 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 188 ∷ [ # 143 ]) , (─ (# 225 ∷ # 188 ∷ [ # 135 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 188 } tt) (toWitness {Q = inRange? 128 191 135 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 188 ∷ [ # 152 ]) , (─ (# 225 ∷ # 188 ∷ [ # 144 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 188 } tt) (toWitness {Q = inRange? 128 191 144 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 188 ∷ [ # 153 ]) , (─ (# 225 ∷ # 188 ∷ [ # 145 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 188 } tt) (toWitness {Q = inRange? 128 191 145 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 188 ∷ [ # 154 ]) , (─ (# 225 ∷ # 188 ∷ [ # 146 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 188 } tt) (toWitness {Q = inRange? 128 191 146 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 188 ∷ [ # 155 ]) , (─ (# 225 ∷ # 188 ∷ [ # 147 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 188 } tt) (toWitness {Q = inRange? 128 191 147 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 188 ∷ [ # 156 ]) , (─ (# 225 ∷ # 188 ∷ [ # 148 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 188 } tt) (toWitness {Q = inRange? 128 191 148 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 188 ∷ [ # 157 ]) , (─ (# 225 ∷ # 188 ∷ [ # 149 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 188 } tt) (toWitness {Q = inRange? 128 191 149 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 188 ∷ [ # 168 ]) , (─ (# 225 ∷ # 188 ∷ [ # 160 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 188 } tt) (toWitness {Q = inRange? 128 191 160 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 188 ∷ [ # 169 ]) , (─ (# 225 ∷ # 188 ∷ [ # 161 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 188 } tt) (toWitness {Q = inRange? 128 191 161 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 188 ∷ [ # 170 ]) , (─ (# 225 ∷ # 188 ∷ [ # 162 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 188 } tt) (toWitness {Q = inRange? 128 191 162 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 188 ∷ [ # 171 ]) , (─ (# 225 ∷ # 188 ∷ [ # 163 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 188 } tt) (toWitness {Q = inRange? 128 191 163 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 188 ∷ [ # 172 ]) , (─ (# 225 ∷ # 188 ∷ [ # 164 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 188 } tt) (toWitness {Q = inRange? 128 191 164 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 188 ∷ [ # 173 ]) , (─ (# 225 ∷ # 188 ∷ [ # 165 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 188 } tt) (toWitness {Q = inRange? 128 191 165 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 188 ∷ [ # 174 ]) , (─ (# 225 ∷ # 188 ∷ [ # 166 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 188 } tt) (toWitness {Q = inRange? 128 191 166 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 188 ∷ [ # 175 ]) , (─ (# 225 ∷ # 188 ∷ [ # 167 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 188 } tt) (toWitness {Q = inRange? 128 191 167 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 188 ∷ [ # 184 ]) , (─ (# 225 ∷ # 188 ∷ [ # 176 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 188 } tt) (toWitness {Q = inRange? 128 191 176 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 188 ∷ [ # 185 ]) , (─ (# 225 ∷ # 188 ∷ [ # 177 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 188 } tt) (toWitness {Q = inRange? 128 191 177 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 188 ∷ [ # 186 ]) , (─ (# 225 ∷ # 188 ∷ [ # 178 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 188 } tt) (toWitness {Q = inRange? 128 191 178 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 188 ∷ [ # 187 ]) , (─ (# 225 ∷ # 188 ∷ [ # 179 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 188 } tt) (toWitness {Q = inRange? 128 191 179 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 188 ∷ [ # 188 ]) , (─ (# 225 ∷ # 188 ∷ [ # 180 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 188 } tt) (toWitness {Q = inRange? 128 191 180 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 188 ∷ [ # 189 ]) , (─ (# 225 ∷ # 188 ∷ [ # 181 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 188 } tt) (toWitness {Q = inRange? 128 191 181 } tt) refl)) nil refl)))
          ∷ []


