{-# OPTIONS --sized-types #-}

open import Armor.Binary
open import Armor.Prelude
open import Armor.Data.Unicode.UTF8.TCB
open import Armor.Data.Unicode.UTF8.Trie
import      Armor.Grammar.IList

module Armor.Data.X509.Semantic.StringPrep.CaseFoldNFKC.M142 where

open Armor.Grammar.IList UInt8

trie₁₄₂ : List (List UInt8 × Exists─ (List UInt8) UTF8)
trie₁₄₂ =  ((# 240 ∷ # 157 ∷ # 157 ∷ [ # 168 ]) , (─ (# 207 ∷ [ # 131 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {Q = inRange? 192 223 207 } tt) (toWitness {Q = inRange? 128 191 131 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 157 ∷ [ # 169 ]) , (─ (# 207 ∷ [ # 132 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {Q = inRange? 192 223 207 } tt) (toWitness {Q = inRange? 128 191 132 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 157 ∷ [ # 170 ]) , (─ (# 207 ∷ [ # 133 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {Q = inRange? 192 223 207 } tt) (toWitness {Q = inRange? 128 191 133 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 157 ∷ [ # 171 ]) , (─ (# 207 ∷ [ # 134 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {Q = inRange? 192 223 207 } tt) (toWitness {Q = inRange? 128 191 134 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 157 ∷ [ # 172 ]) , (─ (# 207 ∷ [ # 135 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {Q = inRange? 192 223 207 } tt) (toWitness {Q = inRange? 128 191 135 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 157 ∷ [ # 173 ]) , (─ (# 207 ∷ [ # 136 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {Q = inRange? 192 223 207 } tt) (toWitness {Q = inRange? 128 191 136 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 157 ∷ [ # 174 ]) , (─ (# 207 ∷ [ # 137 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {Q = inRange? 192 223 207 } tt) (toWitness {Q = inRange? 128 191 137 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 158 ∷ [ # 129 ]) , (─ (# 207 ∷ [ # 131 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {Q = inRange? 192 223 207 } tt) (toWitness {Q = inRange? 128 191 131 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 158 ∷ [ # 144 ]) , (─ (# 206 ∷ [ # 177 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {Q = inRange? 192 223 206 } tt) (toWitness {Q = inRange? 128 191 177 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 158 ∷ [ # 145 ]) , (─ (# 206 ∷ [ # 178 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {Q = inRange? 192 223 206 } tt) (toWitness {Q = inRange? 128 191 178 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 158 ∷ [ # 146 ]) , (─ (# 206 ∷ [ # 179 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {Q = inRange? 192 223 206 } tt) (toWitness {Q = inRange? 128 191 179 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 158 ∷ [ # 147 ]) , (─ (# 206 ∷ [ # 180 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {Q = inRange? 192 223 206 } tt) (toWitness {Q = inRange? 128 191 180 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 158 ∷ [ # 148 ]) , (─ (# 206 ∷ [ # 181 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {Q = inRange? 192 223 206 } tt) (toWitness {Q = inRange? 128 191 181 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 158 ∷ [ # 149 ]) , (─ (# 206 ∷ [ # 182 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {Q = inRange? 192 223 206 } tt) (toWitness {Q = inRange? 128 191 182 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 158 ∷ [ # 150 ]) , (─ (# 206 ∷ [ # 183 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {Q = inRange? 192 223 206 } tt) (toWitness {Q = inRange? 128 191 183 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 158 ∷ [ # 151 ]) , (─ (# 206 ∷ [ # 184 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {Q = inRange? 192 223 206 } tt) (toWitness {Q = inRange? 128 191 184 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 158 ∷ [ # 152 ]) , (─ (# 206 ∷ [ # 185 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {Q = inRange? 192 223 206 } tt) (toWitness {Q = inRange? 128 191 185 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 158 ∷ [ # 153 ]) , (─ (# 206 ∷ [ # 186 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {Q = inRange? 192 223 206 } tt) (toWitness {Q = inRange? 128 191 186 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 158 ∷ [ # 154 ]) , (─ (# 206 ∷ [ # 187 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {Q = inRange? 192 223 206 } tt) (toWitness {Q = inRange? 128 191 187 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 158 ∷ [ # 155 ]) , (─ (# 206 ∷ [ # 188 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {Q = inRange? 192 223 206 } tt) (toWitness {Q = inRange? 128 191 188 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 158 ∷ [ # 156 ]) , (─ (# 206 ∷ [ # 189 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {Q = inRange? 192 223 206 } tt) (toWitness {Q = inRange? 128 191 189 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 158 ∷ [ # 157 ]) , (─ (# 206 ∷ [ # 190 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {Q = inRange? 192 223 206 } tt) (toWitness {Q = inRange? 128 191 190 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 158 ∷ [ # 158 ]) , (─ (# 206 ∷ [ # 191 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {Q = inRange? 192 223 206 } tt) (toWitness {Q = inRange? 128 191 191 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 158 ∷ [ # 159 ]) , (─ (# 207 ∷ [ # 128 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {Q = inRange? 192 223 207 } tt) (toWitness {Q = inRange? 128 191 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 158 ∷ [ # 160 ]) , (─ (# 207 ∷ [ # 129 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {Q = inRange? 192 223 207 } tt) (toWitness {Q = inRange? 128 191 129 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 158 ∷ [ # 161 ]) , (─ (# 206 ∷ [ # 184 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {Q = inRange? 192 223 206 } tt) (toWitness {Q = inRange? 128 191 184 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 158 ∷ [ # 162 ]) , (─ (# 207 ∷ [ # 131 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {Q = inRange? 192 223 207 } tt) (toWitness {Q = inRange? 128 191 131 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 158 ∷ [ # 163 ]) , (─ (# 207 ∷ [ # 132 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {Q = inRange? 192 223 207 } tt) (toWitness {Q = inRange? 128 191 132 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 158 ∷ [ # 164 ]) , (─ (# 207 ∷ [ # 133 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {Q = inRange? 192 223 207 } tt) (toWitness {Q = inRange? 128 191 133 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 158 ∷ [ # 165 ]) , (─ (# 207 ∷ [ # 134 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {Q = inRange? 192 223 207 } tt) (toWitness {Q = inRange? 128 191 134 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 158 ∷ [ # 166 ]) , (─ (# 207 ∷ [ # 135 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {Q = inRange? 192 223 207 } tt) (toWitness {Q = inRange? 128 191 135 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 158 ∷ [ # 167 ]) , (─ (# 207 ∷ [ # 136 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {Q = inRange? 192 223 207 } tt) (toWitness {Q = inRange? 128 191 136 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 158 ∷ [ # 168 ]) , (─ (# 207 ∷ [ # 137 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {Q = inRange? 192 223 207 } tt) (toWitness {Q = inRange? 128 191 137 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 158 ∷ [ # 187 ]) , (─ (# 207 ∷ [ # 131 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {Q = inRange? 192 223 207 } tt) (toWitness {Q = inRange? 128 191 131 } tt) refl)) nil refl)))
          ∷ []


