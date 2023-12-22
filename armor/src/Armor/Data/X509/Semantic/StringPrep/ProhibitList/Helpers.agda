{-# OPTIONS --sized-types #-}

open import Armor.Binary
open import Armor.Prelude
open import Armor.Data.Unicode.UTF8.TCB
open import Armor.Data.Unicode.UTF8.Trie
import      Armor.Grammar.IList

open import Armor.Data.X509.Semantic.StringPrep.ExcludeRange

module Armor.Data.X509.Semantic.StringPrep.ProhibitList.Helpers where

open Armor.Grammar.IList UInt8


module TableC where

  module CasesForUTF82 where
    case1 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case1 c = ⌊ inRangeAndFilter? 2 ((205 , 205 , const ⊤ , (λ x → yes tt)) Vec.∷ (128 , 129 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c ⌋

    check : ∀ {@0 bs} → UTF8Char bs → Bool
    check x = or (List.map (λ f → f x) fs)
      where
      fs : List (∀ {@0 bs} → UTF8Char bs → Bool)
      fs = case1 ∷ []

  module CasesForUTF83 where
    case1 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case1 c = ⌊ inRangeAndFilter? 3 (((226 , 226 , const ⊤ , (λ x → yes tt))) Vec.∷ ((128 , 128 , const ⊤ , (λ x → yes tt))) Vec.∷ (((142 , 143 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case2 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case2 c = ⌊ inRangeAndFilter? 3 (((226 , 226 , const ⊤ , (λ x → yes tt))) Vec.∷ ((128 , 128 , const ⊤ , (λ x → yes tt))) Vec.∷ (((170 , 174 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case3 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case3 c = ⌊ inRangeAndFilter? 3 (((226 , 226 , const ⊤ , (λ x → yes tt))) Vec.∷ ((129 , 129 , const ⊤ , (λ x → yes tt))) Vec.∷ (((170 , 175 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case4 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case4 c = ⌊ inRangeAndFilter? 3 (((238 , 238 , const ⊤ , (λ x → yes tt))) Vec.∷ ((128 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case5 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case5 c = ⌊ inRangeAndFilter? 3 (((239 , 239 , const ⊤ , (λ x → yes tt))) Vec.∷ ((128 , 163 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case6 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case6 c = ⌊ inRangeAndFilter? 3 (((239 , 239 , const ⊤ , (λ x → yes tt))) Vec.∷ ((183 , 183 , const ⊤ , (λ x → yes tt))) Vec.∷ (((144 , 175 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case7 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case7 c = ⌊ inRangeAndFilter? 3 (((239 , 239 , const ⊤ , (λ x → yes tt))) Vec.∷ ((191 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ (((189 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    check : ∀ {@0 bs} → UTF8Char bs → Bool
    check x = or (List.map (λ f → f x) fs)
      where
      fs : List (∀ {@0 bs} → UTF8Char bs → Bool)
      fs = case1 ∷ case2 ∷ case3 ∷ case4 ∷ case5 ∷ case6 ∷ case7 ∷ []

  module CasesForUTF84 where
    case1 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case1 c = ⌊ inRangeAndFilter? 4 (((240 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((159 , 159 , const ⊤ , (λ x → yes tt))) Vec.∷ (((191 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ (((190 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case2 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case2 c = ⌊ inRangeAndFilter? 4 (((240 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((175 , 175 , const ⊤ , (λ x → yes tt))) Vec.∷ (((191 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ (((190 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case3 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case3 c = ⌊ inRangeAndFilter? 4 (((240 , 242 , const ⊤ , (λ x → yes tt))) Vec.∷ (((191 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ (((191 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ (((190 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case4 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case4 c = ⌊ inRangeAndFilter? 4 (((241 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((143 , 143 , const ⊤ , (λ x → yes tt))) Vec.∷ (((191 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ (((190 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case5 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case5 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((176 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case6 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case6 c = ⌊ inRangeAndFilter? 4 (((244 , 244 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 143 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    check : ∀ {@0 bs} → UTF8Char bs → Bool
    check x = or (List.map (λ f → f x) fs)
      where
      fs : List (∀ {@0 bs} → UTF8Char bs → Bool)
      fs = case1 ∷ case2 ∷ case3 ∷ case4 ∷ case5 ∷ case6 ∷ []

  --- for proof, we need to use "any?"

module TableA1 where

  module CasesForUTF82 where
    case1 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case1 c = ⌊ inRangeAndFilter? 2 ((200 , 200 , const ⊤ , (λ x → yes tt)) Vec.∷ (161 , 161 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c ⌋

    case2 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case2 c = ⌊ inRangeAndFilter? 2 ((200 , 200 , const ⊤ , (λ x → yes tt)) Vec.∷ (180 , 191 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c ⌋

    case3 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case3 c = ⌊ inRangeAndFilter? 2 ((201 , 201 , const ⊤ , (λ x → yes tt)) Vec.∷ (128 , 143 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c ⌋

    case4 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case4 c = ⌊ inRangeAndFilter? 2 ((202 , 202 , const ⊤ , (λ x → yes tt)) Vec.∷ (174 , 175 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c ⌋

    case5 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case5 c = ⌊ inRangeAndFilter? 2 ((219 , 219 , const ⊤ , (λ x → yes tt)) Vec.∷ (174 , 175 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c ⌋

    case6 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case6 c = ⌊ inRangeAndFilter? 2 ((203 , 203 , const ⊤ , (λ x → yes tt)) Vec.∷ (175 , 191 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c ⌋

    case7 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case7 c = ⌊ inRangeAndFilter? 2 ((205 , 205 , const ⊤ , (λ x → yes tt)) Vec.∷ (144 , 159 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c ⌋

    case8 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case8 c = ⌊ inRangeAndFilter? 2 ((205 , 205 , const ⊤ , (λ x → yes tt)) Vec.∷ (176 , 179 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c ⌋

    case9 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case9 c = ⌊ inRangeAndFilter? 2 ((205 , 205 , const ⊤ , (λ x → yes tt)) Vec.∷ (182 , 185 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c ⌋

    case10 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case10 c = ⌊ inRangeAndFilter? 2 ((205 , 205 , const ⊤ , (λ x → yes tt)) Vec.∷ (187 , 189 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c ⌋

    case11 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case11 c = ⌊ inRangeAndFilter? 2 ((205 , 205 , const ⊤ , (λ x → yes tt)) Vec.∷ (191 , 191 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c ⌋

    case12 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case12 c = ⌊ inRangeAndFilter? 2 ((219 , 219 , const ⊤ , (λ x → yes tt)) Vec.∷ (191 , 191 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c ⌋

    case13 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case13 c = ⌊ inRangeAndFilter? 2 ((206 , 206 , const ⊤ , (λ x → yes tt)) Vec.∷ (128 , 131 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c ⌋

    case14 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case14 c = ⌊ inRangeAndFilter? 2 ((206 , 206 , const ⊤ , (λ x → yes tt)) Vec.∷ (139 , 139 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c ⌋

    case15 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case15 c = ⌊ inRangeAndFilter? 2 ((206 , 206 , const ⊤ , (λ x → yes tt)) Vec.∷ (141 , 141 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c ⌋

    case16 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case16 c = ⌊ inRangeAndFilter? 2 ((206 , 206 , const ⊤ , (λ x → yes tt)) Vec.∷ (162 , 162 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c ⌋

    case17 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case17 c = ⌊ inRangeAndFilter? 2 ((214 , 214 , const ⊤ , (λ x → yes tt)) Vec.∷ (162 , 162 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c ⌋

    case18 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case18 c = ⌊ inRangeAndFilter? 2 ((207 , 207 , const ⊤ , (λ x → yes tt)) Vec.∷ (143 , 143 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c ⌋

    case19 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case19 c = ⌊ inRangeAndFilter? 2 ((211 , 211 , const ⊤ , (λ x → yes tt)) Vec.∷ (143 , 143 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c ⌋

    case20 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case20 c = ⌊ inRangeAndFilter? 2 ((207 , 207 , const ⊤ , (λ x → yes tt)) Vec.∷ (183 , 191 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c ⌋

    case21 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case21 c = ⌊ inRangeAndFilter? 2 ((210 , 210 , const ⊤ , (λ x → yes tt)) Vec.∷ (135 , 135 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c ⌋

    case22 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case22 c = ⌊ inRangeAndFilter? 2 ((211 , 211 , const ⊤ , (λ x → yes tt)) Vec.∷ (182 , 183 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c ⌋

    case23 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case23 c = ⌊ inRangeAndFilter? 2 ((211 , 211 , const ⊤ , (λ x → yes tt)) Vec.∷ (186 , 191 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c ⌋

    case24 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case24 c = ⌊ inRangeAndFilter? 2 ((212 , 212 , const ⊤ , (λ x → yes tt)) Vec.∷ (144 , 176 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c ⌋

    case25 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case25 c = ⌊ inRangeAndFilter? 2 ((213 , 213 , const ⊤ , (λ x → yes tt)) Vec.∷ (151 , 152 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c ⌋

    case26 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case26 c = ⌊ inRangeAndFilter? 2 ((213 , 213 , const ⊤ , (λ x → yes tt)) Vec.∷ (160 , 160 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c ⌋

    case27 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case27 c = ⌊ inRangeAndFilter? 2 ((216 , 216 , const ⊤ , (λ x → yes tt)) Vec.∷ (160 , 160 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c ⌋

    case28 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case28 c = ⌊ inRangeAndFilter? 2 ((214 , 214 , const ⊤ , (λ x → yes tt)) Vec.∷ (136 , 136 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c ⌋

    case29 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case29 c = ⌊ inRangeAndFilter? 2 ((214 , 214 , const ⊤ , (λ x → yes tt)) Vec.∷ (139 , 144 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c ⌋

    case30 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case30 c = ⌊ inRangeAndFilter? 2 ((214 , 214 , const ⊤ , (λ x → yes tt)) Vec.∷ (186 , 186 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c ⌋

    case31 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case31 c = ⌊ inRangeAndFilter? 2 ((215 , 215 , const ⊤ , (λ x → yes tt)) Vec.∷ (133 , 143 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c ⌋

    case32 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case32 c = ⌊ inRangeAndFilter? 2 ((215 , 215 , const ⊤ , (λ x → yes tt)) Vec.∷ (171 , 175 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c ⌋

    case33 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case33 c = ⌊ inRangeAndFilter? 2 ((215 , 215 , const ⊤ , (λ x → yes tt)) Vec.∷ (181 , 191 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c ⌋

    case34 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case34 c = ⌊ inRangeAndFilter? 2 ((216 , 216 , const ⊤ , (λ x → yes tt)) Vec.∷ (128 , 139 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c ⌋

    case35 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case35 c = ⌊ inRangeAndFilter? 2 ((216 , 216 , const ⊤ , (λ x → yes tt)) Vec.∷ (141 , 154 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c ⌋

    case36 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case36 c = ⌊ inRangeAndFilter? 2 ((216 , 216 , const ⊤ , (λ x → yes tt)) Vec.∷ (156 , 158 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c ⌋

    case37 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case37 c = ⌊ inRangeAndFilter? 2 ((216 , 216 , const ⊤ , (λ x → yes tt)) Vec.∷ (187 , 191 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c ⌋

    case38 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case38 c = ⌊ inRangeAndFilter? 2 ((217 , 217 , const ⊤ , (λ x → yes tt)) Vec.∷ (150 , 159 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c ⌋

    case39 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case39 c = ⌊ inRangeAndFilter? 2 ((220 , 220 , const ⊤ , (λ x → yes tt)) Vec.∷ (142 , 142 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c ⌋

    case40 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case40 c = ⌊ inRangeAndFilter? 2 ((220 , 220 , const ⊤ , (λ x → yes tt)) Vec.∷ (173 , 175 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c ⌋

    case41 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case41 c = ⌊ inRangeAndFilter? 2 ((221 , 221 , const ⊤ , (λ x → yes tt)) Vec.∷ (139 , 191 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c ⌋

    case42 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case42 c = ⌊ inRangeAndFilter? 2 ((222 , 222 , const ⊤ , (λ x → yes tt)) Vec.∷ (178 , 191 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c ⌋

    case43 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case43 c = ⌊ inRangeAndFilter? 2 ((223 , 223 , const ⊤ , (λ x → yes tt)) Vec.∷ (128 , 191 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c ⌋

    check : ∀ {@0 bs} → UTF8Char bs → Bool
    check x = or (List.map (λ f → f x) fs)
      where
      fs : List (∀ {@0 bs} → UTF8Char bs → Bool)
      fs = case1 ∷ case2 ∷ case3 ∷ case4 ∷ case5 ∷ case6 ∷ case7 ∷ case8 ∷ case9 ∷ case10 ∷ case11 ∷ case12 ∷ case13 ∷ case14 ∷ case15 ∷ case16 ∷ case17 ∷ case18 ∷ case19 ∷ case20 ∷ case21 ∷ case22 ∷ case23 ∷ case24 ∷ case25 ∷ case26 ∷ case27 ∷ case28 ∷ case29 ∷ case30 ∷ case31 ∷ case32 ∷ case33 ∷ case34 ∷ case35 ∷ case36 ∷ case37 ∷ case38 ∷ case39 ∷ case40 ∷ case41 ∷ case42 ∷ case43 ∷ []

  module CasesForUTF83 where
    case1 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case1 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((160 , 163 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case2 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case2 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((164 , 164 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 128 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case3 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case3 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((166 , 166 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 128 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case4 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case4 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((170 , 170 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 128 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case5 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case5 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((172 , 172 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 128 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case6 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case6 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((176 , 176 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 128 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case7 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case7 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((184 , 184 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 128 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case8 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case8 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((186 , 186 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 128 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case9 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case9 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((164 , 164 , const ⊤ , (λ x → yes tt))) Vec.∷ (((132 , 132 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case10 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case10 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((166 , 166 , const ⊤ , (λ x → yes tt))) Vec.∷ (((132 , 132 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case11 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case11 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((170 , 170 , const ⊤ , (λ x → yes tt))) Vec.∷ (((132 , 132 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case12 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case12 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((172 , 172 , const ⊤ , (λ x → yes tt))) Vec.∷ (((132 , 132 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case13 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case13 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((174 , 174 , const ⊤ , (λ x → yes tt))) Vec.∷ (((132 , 132 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case14 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case14 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((176 , 176 , const ⊤ , (λ x → yes tt))) Vec.∷ (((132 , 132 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case15 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case15 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((178 , 178 , const ⊤ , (λ x → yes tt))) Vec.∷ (((132 , 132 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case16 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case16 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((180 , 180 , const ⊤ , (λ x → yes tt))) Vec.∷ (((132 , 132 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case17 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case17 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((182 , 182 , const ⊤ , (λ x → yes tt))) Vec.∷ (((132 , 132 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case18 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case18 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((164 , 164 , const ⊤ , (λ x → yes tt))) Vec.∷ (((186 , 187 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case19 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case19 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((166 , 166 , const ⊤ , (λ x → yes tt))) Vec.∷ (((186 , 187 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case20 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case20 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((168 , 168 , const ⊤ , (λ x → yes tt))) Vec.∷ (((186 , 187 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case21 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case21 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((170 , 170 , const ⊤ , (λ x → yes tt))) Vec.∷ (((186 , 187 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case22 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case22 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((172 , 172 , const ⊤ , (λ x → yes tt))) Vec.∷ (((186 , 187 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case23 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case23 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((165 , 165 , const ⊤ , (λ x → yes tt))) Vec.∷ (((142 , 143 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case24 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case24 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((171 , 171 , const ⊤ , (λ x → yes tt))) Vec.∷ (((142 , 143 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case25 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case25 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((187 , 187 , const ⊤ , (λ x → yes tt))) Vec.∷ (((142 , 143 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case26 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case26 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((165 , 165 , const ⊤ , (λ x → yes tt))) Vec.∷ (((149 , 151 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case27 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case27 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((165 , 165 , const ⊤ , (λ x → yes tt))) Vec.∷ (((177 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case28 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case28 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((173 , 173 , const ⊤ , (λ x → yes tt))) Vec.∷ (((177 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case29 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case29 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((166 , 166 , const ⊤ , (λ x → yes tt))) Vec.∷ (((141 , 142 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case30 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case30 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((172 , 172 , const ⊤ , (λ x → yes tt))) Vec.∷ (((141 , 142 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case31 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case31 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((191 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ (((141 , 142 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case32 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case32 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((166 , 166 , const ⊤ , (λ x → yes tt))) Vec.∷ (((145 , 146 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case33 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case33 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((168 , 168 , const ⊤ , (λ x → yes tt))) Vec.∷ (((145 , 146 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case34 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case34 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((172 , 172 , const ⊤ , (λ x → yes tt))) Vec.∷ (((145 , 146 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case35 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case35 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((166 , 166 , const ⊤ , (λ x → yes tt))) Vec.∷ (((169 , 169 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case36 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case36 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((168 , 168 , const ⊤ , (λ x → yes tt))) Vec.∷ (((169 , 169 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case37 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case37 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((170 , 170 , const ⊤ , (λ x → yes tt))) Vec.∷ (((169 , 169 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case38 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case38 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((172 , 172 , const ⊤ , (λ x → yes tt))) Vec.∷ (((169 , 169 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case39 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case39 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((176 , 176 , const ⊤ , (λ x → yes tt))) Vec.∷ (((169 , 169 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case40 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case40 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((178 , 178 , const ⊤ , (λ x → yes tt))) Vec.∷ (((169 , 169 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case41 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case41 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((180 , 180 , const ⊤ , (λ x → yes tt))) Vec.∷ (((169 , 169 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case42 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case42 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((166 , 166 , const ⊤ , (λ x → yes tt))) Vec.∷ (((177 , 177 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case43 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case43 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((168 , 168 , const ⊤ , (λ x → yes tt))) Vec.∷ (((177 , 177 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case44 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case44 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((170 , 170 , const ⊤ , (λ x → yes tt))) Vec.∷ (((177 , 177 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case45 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case45 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((172 , 172 , const ⊤ , (λ x → yes tt))) Vec.∷ (((177 , 177 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case46 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case46 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((166 , 166 , const ⊤ , (λ x → yes tt))) Vec.∷ (((179 , 181 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case47 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case47 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((166 , 166 , const ⊤ , (λ x → yes tt))) Vec.∷ (((189 , 189 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case48 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case48 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((168 , 168 , const ⊤ , (λ x → yes tt))) Vec.∷ (((189 , 189 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case49 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case49 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((190 , 190 , const ⊤ , (λ x → yes tt))) Vec.∷ (((189 , 189 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case50 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case50 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((167 , 167 , const ⊤ , (λ x → yes tt))) Vec.∷ (((133 , 134 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case51 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case51 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((186 , 186 , const ⊤ , (λ x → yes tt))) Vec.∷ (((133 , 134 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case52 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case52 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((167 , 167 , const ⊤ , (λ x → yes tt))) Vec.∷ (((137 , 138 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case53 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case53 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((169 , 169 , const ⊤ , (λ x → yes tt))) Vec.∷ (((137 , 138 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case54 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case54 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((173 , 173 , const ⊤ , (λ x → yes tt))) Vec.∷ (((137 , 138 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case55 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case55 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((167 , 167 , const ⊤ , (λ x → yes tt))) Vec.∷ (((142 , 150 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case56 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case56 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((175 , 175 , const ⊤ , (λ x → yes tt))) Vec.∷ (((142 , 150 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case57 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case57 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((181 , 181 , const ⊤ , (λ x → yes tt))) Vec.∷ (((142 , 150 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case58 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case58 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((167 , 167 , const ⊤ , (λ x → yes tt))) Vec.∷ (((152 , 155 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case59 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case59 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((173 , 173 , const ⊤ , (λ x → yes tt))) Vec.∷ (((152 , 155 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case60 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case60 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((167 , 167 , const ⊤ , (λ x → yes tt))) Vec.∷ (((158 , 158 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case61 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case61 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((173 , 173 , const ⊤ , (λ x → yes tt))) Vec.∷ (((158 , 158 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case62 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case62 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((167 , 167 , const ⊤ , (λ x → yes tt))) Vec.∷ (((164 , 165 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case63 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case63 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((167 , 167 , const ⊤ , (λ x → yes tt))) Vec.∷ (((187 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case64 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case64 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((168 , 168 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 129 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case65 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case65 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((174 , 174 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 129 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case66 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case66 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((178 , 178 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 129 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case67 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case67 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((180 , 180 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 129 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case68 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case68 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((182 , 182 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 129 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case69 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case69 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((168 , 168 , const ⊤ , (λ x → yes tt))) Vec.∷ (((131 , 132 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case70 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case70 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((168 , 168 , const ⊤ , (λ x → yes tt))) Vec.∷ (((139 , 142 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case71 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case71 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((183 , 183 , const ⊤ , (λ x → yes tt))) Vec.∷ (((139 , 142 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case72 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case72 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((168 , 168 , const ⊤ , (λ x → yes tt))) Vec.∷ (((180 , 180 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case73 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case73 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((170 , 170 , const ⊤ , (λ x → yes tt))) Vec.∷ (((180 , 180 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case74 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case74 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((176 , 176 , const ⊤ , (λ x → yes tt))) Vec.∷ (((180 , 180 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case75 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case75 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((178 , 178 , const ⊤ , (λ x → yes tt))) Vec.∷ (((180 , 180 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case76 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case76 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((168 , 168 , const ⊤ , (λ x → yes tt))) Vec.∷ (((183 , 183 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case77 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case77 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((169 , 169 , const ⊤ , (λ x → yes tt))) Vec.∷ (((131 , 134 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case78 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case78 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((169 , 169 , const ⊤ , (λ x → yes tt))) Vec.∷ (((142 , 152 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case79 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case79 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((169 , 169 , const ⊤ , (λ x → yes tt))) Vec.∷ (((157 , 157 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case80 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case80 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((174 , 174 , const ⊤ , (λ x → yes tt))) Vec.∷ (((157 , 157 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case81 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case81 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((169 , 169 , const ⊤ , (λ x → yes tt))) Vec.∷ (((159 , 165 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case82 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case82 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((169 , 169 , const ⊤ , (λ x → yes tt))) Vec.∷ (((181 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case83 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case83 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((183 , 183 , const ⊤ , (λ x → yes tt))) Vec.∷ (((181 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case84 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case84 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((170 , 170 , const ⊤ , (λ x → yes tt))) Vec.∷ (((140 , 140 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case85 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case85 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((170 , 170 , const ⊤ , (λ x → yes tt))) Vec.∷ (((142 , 142 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case86 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case86 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((170 , 170 , const ⊤ , (λ x → yes tt))) Vec.∷ (((146 , 146 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case87 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case87 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((171 , 171 , const ⊤ , (λ x → yes tt))) Vec.∷ (((134 , 134 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case88 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case88 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((171 , 171 , const ⊤ , (λ x → yes tt))) Vec.∷ (((138 , 138 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case89 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case89 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((171 , 171 , const ⊤ , (λ x → yes tt))) Vec.∷ (((145 , 159 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case90 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case90 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((171 , 171 , const ⊤ , (λ x → yes tt))) Vec.∷ (((161 , 165 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case91 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case91 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((171 , 171 , const ⊤ , (λ x → yes tt))) Vec.∷ (((176 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case92 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case92 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((177 , 177 , const ⊤ , (λ x → yes tt))) Vec.∷ (((176 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case93 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case93 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((179 , 179 , const ⊤ , (λ x → yes tt))) Vec.∷ (((176 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case94 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case94 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((181 , 181 , const ⊤ , (λ x → yes tt))) Vec.∷ (((176 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case95 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case95 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((172 , 172 , const ⊤ , (λ x → yes tt))) Vec.∷ (((180 , 181 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case96 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case96 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((173 , 173 , const ⊤ , (λ x → yes tt))) Vec.∷ (((132 , 134 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case97 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case97 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((173 , 173 , const ⊤ , (λ x → yes tt))) Vec.∷ (((142 , 149 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case98 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case98 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((173 , 173 , const ⊤ , (λ x → yes tt))) Vec.∷ (((162 , 165 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case99 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case99 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((177 , 177 , const ⊤ , (λ x → yes tt))) Vec.∷ (((162 , 165 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case100 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case100 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((179 , 179 , const ⊤ , (λ x → yes tt))) Vec.∷ (((162 , 165 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case101 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case101 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((181 , 181 , const ⊤ , (λ x → yes tt))) Vec.∷ (((162 , 165 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case102 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case102 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((174 , 174 , const ⊤ , (λ x → yes tt))) Vec.∷ (((139 , 141 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case103 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case103 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((174 , 174 , const ⊤ , (λ x → yes tt))) Vec.∷ (((145 , 145 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case104 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case104 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((176 , 176 , const ⊤ , (λ x → yes tt))) Vec.∷ (((145 , 145 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case105 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case105 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((178 , 178 , const ⊤ , (λ x → yes tt))) Vec.∷ (((145 , 145 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case106 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case106 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((180 , 180 , const ⊤ , (λ x → yes tt))) Vec.∷ (((145 , 145 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case107 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case107 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((174 , 174 , const ⊤ , (λ x → yes tt))) Vec.∷ (((150 , 152 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case108 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case108 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((174 , 174 , const ⊤ , (λ x → yes tt))) Vec.∷ (((155 , 155 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case109 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case109 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((174 , 174 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 162 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case110 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case110 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((174 , 174 , const ⊤ , (λ x → yes tt))) Vec.∷ (((165 , 167 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case111 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case111 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((174 , 174 , const ⊤ , (λ x → yes tt))) Vec.∷ (((171 , 173 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case112 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case112 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((174 , 174 , const ⊤ , (λ x → yes tt))) Vec.∷ (((182 , 182 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case113 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case113 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((174 , 174 , const ⊤ , (λ x → yes tt))) Vec.∷ (((186 , 189 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case114 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case114 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((176 , 176 , const ⊤ , (λ x → yes tt))) Vec.∷ (((186 , 189 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case115 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case115 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((178 , 178 , const ⊤ , (λ x → yes tt))) Vec.∷ (((186 , 189 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case116 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case116 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((180 , 180 , const ⊤ , (λ x → yes tt))) Vec.∷ (((186 , 189 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case117 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case117 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((175 , 175 , const ⊤ , (λ x → yes tt))) Vec.∷ (((131 , 133 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case118 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case118 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((175 , 175 , const ⊤ , (λ x → yes tt))) Vec.∷ (((137 , 137 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case119 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case119 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((177 , 177 , const ⊤ , (λ x → yes tt))) Vec.∷ (((137 , 137 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case120 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case120 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((179 , 179 , const ⊤ , (λ x → yes tt))) Vec.∷ (((137 , 137 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case121 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case121 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((181 , 181 , const ⊤ , (λ x → yes tt))) Vec.∷ (((137 , 137 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case122 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case122 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((186 , 186 , const ⊤ , (λ x → yes tt))) Vec.∷ (((137 , 137 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case123 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case123 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((175 , 175 , const ⊤ , (λ x → yes tt))) Vec.∷ (((152 , 166 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case124 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case124 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((175 , 175 , const ⊤ , (λ x → yes tt))) Vec.∷ (((179 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case125 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case125 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((176 , 176 , const ⊤ , (λ x → yes tt))) Vec.∷ (((141 , 141 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case126 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case126 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((178 , 178 , const ⊤ , (λ x → yes tt))) Vec.∷ (((141 , 141 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case127 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case127 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((180 , 180 , const ⊤ , (λ x → yes tt))) Vec.∷ (((141 , 141 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case128 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case128 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((177 , 177 , const ⊤ , (λ x → yes tt))) Vec.∷ (((133 , 133 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case129 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case129 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((179 , 179 , const ⊤ , (λ x → yes tt))) Vec.∷ (((133 , 133 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case130 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case130 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((187 , 187 , const ⊤ , (λ x → yes tt))) Vec.∷ (((133 , 133 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case131 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case131 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((177 , 177 , const ⊤ , (λ x → yes tt))) Vec.∷ (((142 , 148 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case132 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case132 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((179 , 179 , const ⊤ , (λ x → yes tt))) Vec.∷ (((142 , 148 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case133 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case133 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((177 , 177 , const ⊤ , (λ x → yes tt))) Vec.∷ (((151 , 159 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case134 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case134 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((179 , 179 , const ⊤ , (λ x → yes tt))) Vec.∷ (((151 , 157 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case135 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case135 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((179 , 179 , const ⊤ , (λ x → yes tt))) Vec.∷ (((159 , 159 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case136 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case136 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((181 , 181 , const ⊤ , (λ x → yes tt))) Vec.∷ (((132 , 133 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case137 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case137 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((181 , 181 , const ⊤ , (λ x → yes tt))) Vec.∷ (((152 , 159 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case138 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case138 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((182 , 182 , const ⊤ , (λ x → yes tt))) Vec.∷ (((151 , 153 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case139 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case139 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((182 , 182 , const ⊤ , (λ x → yes tt))) Vec.∷ (((178 , 178 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case140 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case140 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((182 , 182 , const ⊤ , (λ x → yes tt))) Vec.∷ (((188 , 188 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case141 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case141 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((182 , 182 , const ⊤ , (λ x → yes tt))) Vec.∷ (((190 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case142 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case142 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((186 , 186 , const ⊤ , (λ x → yes tt))) Vec.∷ (((190 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case143 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case143 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((183 , 183 , const ⊤ , (λ x → yes tt))) Vec.∷ (((135 , 137 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case144 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case144 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((183 , 183 , const ⊤ , (λ x → yes tt))) Vec.∷ (((149 , 149 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case145 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case145 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((183 , 183 , const ⊤ , (λ x → yes tt))) Vec.∷ (((151 , 151 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case146 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case146 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((183 , 183 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 177 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case147 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case147 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((184 , 184 , const ⊤ , (λ x → yes tt))) Vec.∷ (((187 , 190 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case148 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case148 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((185 , 185 , const ⊤ , (λ x → yes tt))) Vec.∷ (((156 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case149 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case149 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((186 , 186 , const ⊤ , (λ x → yes tt))) Vec.∷ (((131 , 131 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case150 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case150 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((186 , 186 , const ⊤ , (λ x → yes tt))) Vec.∷ (((139 , 140 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case151 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case151 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((186 , 186 , const ⊤ , (λ x → yes tt))) Vec.∷ (((142 , 147 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case152 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case152 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((186 , 186 , const ⊤ , (λ x → yes tt))) Vec.∷ (((152 , 152 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case153 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case153 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((190 , 190 , const ⊤ , (λ x → yes tt))) Vec.∷ (((152 , 152 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case154 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case154 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((186 , 186 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case155 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case155 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((186 , 186 , const ⊤ , (λ x → yes tt))) Vec.∷ (((164 , 164 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case156 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case156 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((186 , 186 , const ⊤ , (λ x → yes tt))) Vec.∷ (((166 , 166 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case157 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case157 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((186 , 186 , const ⊤ , (λ x → yes tt))) Vec.∷ (((168 , 169 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case158 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case158 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((186 , 186 , const ⊤ , (λ x → yes tt))) Vec.∷ (((172 , 172 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case159 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case159 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((186 , 186 , const ⊤ , (λ x → yes tt))) Vec.∷ (((186 , 186 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case160 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case160 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((187 , 187 , const ⊤ , (λ x → yes tt))) Vec.∷ (((135 , 135 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case161 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case161 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((187 , 187 , const ⊤ , (λ x → yes tt))) Vec.∷ (((154 , 155 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case162 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case162 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((187 , 187 , const ⊤ , (λ x → yes tt))) Vec.∷ (((158 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case163 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case163 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((189 , 189 , const ⊤ , (λ x → yes tt))) Vec.∷ (((136 , 136 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case164 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case164 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((189 , 189 , const ⊤ , (λ x → yes tt))) Vec.∷ (((171 , 176 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case165 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case165 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((190 , 190 , const ⊤ , (λ x → yes tt))) Vec.∷ (((140 , 143 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case166 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case166 c = ⌊ inRangeAndFilter? 3 (((224 , 224 , const ⊤ , (λ x → yes tt))) Vec.∷ ((191 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ (((144 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case167 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case167 c = ⌊ inRangeAndFilter? 3 (((225 , 225 , const ⊤ , (λ x → yes tt))) Vec.∷ ((128 , 128 , const ⊤ , (λ x → yes tt))) Vec.∷ (((162 , 162 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case168 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case168 c = ⌊ inRangeAndFilter? 3 (((225 , 225 , const ⊤ , (λ x → yes tt))) Vec.∷ ((128 , 128 , const ⊤ , (λ x → yes tt))) Vec.∷ (((168 , 168 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case169 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case169 c = ⌊ inRangeAndFilter? 3 (((225 , 225 , const ⊤ , (λ x → yes tt))) Vec.∷ ((128 , 128 , const ⊤ , (λ x → yes tt))) Vec.∷ (((171 , 171 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case170 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case170 c = ⌊ inRangeAndFilter? 3 (((225 , 225 , const ⊤ , (λ x → yes tt))) Vec.∷ ((128 , 128 , const ⊤ , (λ x → yes tt))) Vec.∷ (((179 , 181 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case171 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case171 c = ⌊ inRangeAndFilter? 3 (((225 , 225 , const ⊤ , (λ x → yes tt))) Vec.∷ ((128 , 128 , const ⊤ , (λ x → yes tt))) Vec.∷ (((186 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case172 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case172 c = ⌊ inRangeAndFilter? 3 (((225 , 225 , const ⊤ , (λ x → yes tt))) Vec.∷ ((135 , 135 , const ⊤ , (λ x → yes tt))) Vec.∷ (((186 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case173 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case173 c = ⌊ inRangeAndFilter? 3 (((225 , 225 , const ⊤ , (λ x → yes tt))) Vec.∷ ((187 , 187 , const ⊤ , (λ x → yes tt))) Vec.∷ (((186 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case174 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case174 c = ⌊ inRangeAndFilter? 3 (((225 , 225 , const ⊤ , (λ x → yes tt))) Vec.∷ ((129 , 129 , const ⊤ , (λ x → yes tt))) Vec.∷ (((154 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case175 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case175 c = ⌊ inRangeAndFilter? 3 (((225 , 225 , const ⊤ , (λ x → yes tt))) Vec.∷ ((130 , 130 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 159 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case176 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case176 c = ⌊ inRangeAndFilter? 3 (((225 , 225 , const ⊤ , (λ x → yes tt))) Vec.∷ ((142 , 142 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 159 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case177 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case177 c = ⌊ inRangeAndFilter? 3 (((225 , 225 , const ⊤ , (λ x → yes tt))) Vec.∷ ((131 , 131 , const ⊤ , (λ x → yes tt))) Vec.∷ (((134 , 143 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case178 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case178 c = ⌊ inRangeAndFilter? 3 (((225 , 225 , const ⊤ , (λ x → yes tt))) Vec.∷ ((131 , 131 , const ⊤ , (λ x → yes tt))) Vec.∷ (((185 , 186 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case179 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case179 c = ⌊ inRangeAndFilter? 3 (((225 , 225 , const ⊤ , (λ x → yes tt))) Vec.∷ ((131 , 131 , const ⊤ , (λ x → yes tt))) Vec.∷ (((188 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case180 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case180 c = ⌊ inRangeAndFilter? 3 (((225 , 225 , const ⊤ , (λ x → yes tt))) Vec.∷ ((133 , 133 , const ⊤ , (λ x → yes tt))) Vec.∷ (((154 , 158 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case181 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case181 c = ⌊ inRangeAndFilter? 3 (((225 , 225 , const ⊤ , (λ x → yes tt))) Vec.∷ ((134 , 134 , const ⊤ , (λ x → yes tt))) Vec.∷ (((163 , 167 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case182 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case182 c = ⌊ inRangeAndFilter? 3 (((225 , 225 , const ⊤ , (λ x → yes tt))) Vec.∷ ((136 , 138 , const ⊤ , (λ x → yes tt))) Vec.∷ (((135 , 135 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case183 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case183 c = ⌊ inRangeAndFilter? 3 (((225 , 225 , const ⊤ , (λ x → yes tt))) Vec.∷ ((141 , 141 , const ⊤ , (λ x → yes tt))) Vec.∷ (((135 , 135 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case184 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case184 c = ⌊ inRangeAndFilter? 3 (((225 , 225 , const ⊤ , (λ x → yes tt))) Vec.∷ ((137 , 138 , const ⊤ , (λ x → yes tt))) Vec.∷ (((137 , 137 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case185 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case185 c = ⌊ inRangeAndFilter? 3 (((225 , 225 , const ⊤ , (λ x → yes tt))) Vec.∷ ((137 , 138 , const ⊤ , (λ x → yes tt))) Vec.∷ (((142 , 143 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case186 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case186 c = ⌊ inRangeAndFilter? 3 (((225 , 225 , const ⊤ , (λ x → yes tt))) Vec.∷ ((189 , 189 , const ⊤ , (λ x → yes tt))) Vec.∷ (((142 , 143 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case187 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case187 c = ⌊ inRangeAndFilter? 3 (((225 , 225 , const ⊤ , (λ x → yes tt))) Vec.∷ ((137 , 137 , const ⊤ , (λ x → yes tt))) Vec.∷ (((151 , 151 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case188 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case188 c = ⌊ inRangeAndFilter? 3 (((225 , 225 , const ⊤ , (λ x → yes tt))) Vec.∷ ((139 , 139 , const ⊤ , (λ x → yes tt))) Vec.∷ (((151 , 151 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case189 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case189 c = ⌊ inRangeAndFilter? 3 (((225 , 225 , const ⊤ , (λ x → yes tt))) Vec.∷ ((137 , 137 , const ⊤ , (λ x → yes tt))) Vec.∷ (((153 , 153 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case190 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case190 c = ⌊ inRangeAndFilter? 3 (((225 , 225 , const ⊤ , (λ x → yes tt))) Vec.∷ ((137 , 137 , const ⊤ , (λ x → yes tt))) Vec.∷ (((158 , 159 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case191 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case191 c = ⌊ inRangeAndFilter? 3 (((225 , 225 , const ⊤ , (λ x → yes tt))) Vec.∷ ((188 , 188 , const ⊤ , (λ x → yes tt))) Vec.∷ (((158 , 159 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case192 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case192 c = ⌊ inRangeAndFilter? 3 (((225 , 225 , const ⊤ , (λ x → yes tt))) Vec.∷ ((138 , 139 , const ⊤ , (λ x → yes tt))) Vec.∷ (((175 , 175 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case193 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case193 c = ⌊ inRangeAndFilter? 3 (((225 , 225 , const ⊤ , (λ x → yes tt))) Vec.∷ ((138 , 138 , const ⊤ , (λ x → yes tt))) Vec.∷ (((177 , 177 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case194 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case194 c = ⌊ inRangeAndFilter? 3 (((225 , 225 , const ⊤ , (λ x → yes tt))) Vec.∷ ((157 , 157 , const ⊤ , (λ x → yes tt))) Vec.∷ (((177 , 177 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case195 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case195 c = ⌊ inRangeAndFilter? 3 (((225 , 225 , const ⊤ , (λ x → yes tt))) Vec.∷ ((138 , 138 , const ⊤ , (λ x → yes tt))) Vec.∷ (((182 , 183 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case196 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case196 c = ⌊ inRangeAndFilter? 3 (((225 , 225 , const ⊤ , (λ x → yes tt))) Vec.∷ ((138 , 138 , const ⊤ , (λ x → yes tt))) Vec.∷ (((191 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case197 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case197 c = ⌊ inRangeAndFilter? 3 (((225 , 225 , const ⊤ , (λ x → yes tt))) Vec.∷ ((191 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ (((191 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case198 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case198 c = ⌊ inRangeAndFilter? 3 (((225 , 225 , const ⊤ , (λ x → yes tt))) Vec.∷ ((139 , 139 , const ⊤ , (λ x → yes tt))) Vec.∷ (((129 , 129 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case199 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case199 c = ⌊ inRangeAndFilter? 3 (((225 , 225 , const ⊤ , (λ x → yes tt))) Vec.∷ ((139 , 139 , const ⊤ , (λ x → yes tt))) Vec.∷ (((134 , 135 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case200 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case200 c = ⌊ inRangeAndFilter? 3 (((225 , 225 , const ⊤ , (λ x → yes tt))) Vec.∷ ((189 , 189 , const ⊤ , (λ x → yes tt))) Vec.∷ (((134 , 135 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case201 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case201 c = ⌊ inRangeAndFilter? 3 (((225 , 225 , const ⊤ , (λ x → yes tt))) Vec.∷ ((139 , 140 , const ⊤ , (λ x → yes tt))) Vec.∷ (((143 , 143 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case202 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case202 c = ⌊ inRangeAndFilter? 3 (((225 , 225 , const ⊤ , (λ x → yes tt))) Vec.∷ ((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((143 , 143 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case203 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case203 c = ⌊ inRangeAndFilter? 3 (((225 , 225 , const ⊤ , (λ x → yes tt))) Vec.∷ ((140 , 140 , const ⊤ , (λ x → yes tt))) Vec.∷ (((145 , 145 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case204 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case204 c = ⌊ inRangeAndFilter? 3 (((225 , 225 , const ⊤ , (λ x → yes tt))) Vec.∷ ((140 , 140 , const ⊤ , (λ x → yes tt))) Vec.∷ (((150 , 151 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case205 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case205 c = ⌊ inRangeAndFilter? 3 (((225 , 225 , const ⊤ , (λ x → yes tt))) Vec.∷ ((188 , 188 , const ⊤ , (λ x → yes tt))) Vec.∷ (((150 , 151 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case206 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case206 c = ⌊ inRangeAndFilter? 3 (((225 , 225 , const ⊤ , (λ x → yes tt))) Vec.∷ ((140 , 140 , const ⊤ , (λ x → yes tt))) Vec.∷ (((159 , 159 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case207 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case207 c = ⌊ inRangeAndFilter? 3 (((225 , 225 , const ⊤ , (λ x → yes tt))) Vec.∷ ((141 , 141 , const ⊤ , (λ x → yes tt))) Vec.∷ (((155 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case208 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case208 c = ⌊ inRangeAndFilter? 3 (((225 , 225 , const ⊤ , (λ x → yes tt))) Vec.∷ ((141 , 141 , const ⊤ , (λ x → yes tt))) Vec.∷ (((189 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case209 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case209 c = ⌊ inRangeAndFilter? 3 (((225 , 225 , const ⊤ , (λ x → yes tt))) Vec.∷ ((143 , 143 , const ⊤ , (λ x → yes tt))) Vec.∷ (((181 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case210 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case210 c = ⌊ inRangeAndFilter? 3 (((225 , 225 , const ⊤ , (λ x → yes tt))) Vec.∷ ((144 , 144 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 128 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case211 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case211 c = ⌊ inRangeAndFilter? 3 (((225 , 225 , const ⊤ , (λ x → yes tt))) Vec.∷ ((153 , 153 , const ⊤ , (λ x → yes tt))) Vec.∷ (((183 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case212 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case212 c = ⌊ inRangeAndFilter? 3 (((225 , 225 , const ⊤ , (λ x → yes tt))) Vec.∷ ((156 , 156 , const ⊤ , (λ x → yes tt))) Vec.∷ (((183 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case213 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case213 c = ⌊ inRangeAndFilter? 3 (((225 , 225 , const ⊤ , (λ x → yes tt))) Vec.∷ ((154 , 154 , const ⊤ , (λ x → yes tt))) Vec.∷ (((157 , 159 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case214 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case214 c = ⌊ inRangeAndFilter? 3 (((225 , 225 , const ⊤ , (λ x → yes tt))) Vec.∷ ((159 , 159 , const ⊤ , (λ x → yes tt))) Vec.∷ (((157 , 159 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case215 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case215 c = ⌊ inRangeAndFilter? 3 (((225 , 225 , const ⊤ , (λ x → yes tt))) Vec.∷ ((155 , 155 , const ⊤ , (λ x → yes tt))) Vec.∷ (((177 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case216 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case216 c = ⌊ inRangeAndFilter? 3 (((225 , 225 , const ⊤ , (λ x → yes tt))) Vec.∷ ((156 , 156 , const ⊤ , (λ x → yes tt))) Vec.∷ (((141 , 141 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case217 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case217 c = ⌊ inRangeAndFilter? 3 (((225 , 225 , const ⊤ , (λ x → yes tt))) Vec.∷ ((156 , 156 , const ⊤ , (λ x → yes tt))) Vec.∷ (((149 , 159 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case218 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case218 c = ⌊ inRangeAndFilter? 3 (((225 , 225 , const ⊤ , (λ x → yes tt))) Vec.∷ ((157 , 157 , const ⊤ , (λ x → yes tt))) Vec.∷ (((148 , 159 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case219 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case219 c = ⌊ inRangeAndFilter? 3 (((225 , 225 , const ⊤ , (λ x → yes tt))) Vec.∷ ((157 , 157 , const ⊤ , (λ x → yes tt))) Vec.∷ (((173 , 173 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case220 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case220 c = ⌊ inRangeAndFilter? 3 (((225 , 225 , const ⊤ , (λ x → yes tt))) Vec.∷ ((157 , 157 , const ⊤ , (λ x → yes tt))) Vec.∷ (((180 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case221 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case221 c = ⌊ inRangeAndFilter? 3 (((225 , 225 , const ⊤ , (λ x → yes tt))) Vec.∷ ((159 , 159 , const ⊤ , (λ x → yes tt))) Vec.∷ (((170 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case222 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case222 c = ⌊ inRangeAndFilter? 3 (((225 , 225 , const ⊤ , (λ x → yes tt))) Vec.∷ ((162 , 162 , const ⊤ , (λ x → yes tt))) Vec.∷ (((170 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case223 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case223 c = ⌊ inRangeAndFilter? 3 (((225 , 225 , const ⊤ , (λ x → yes tt))) Vec.∷ ((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((154 , 159 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case224 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case224 c = ⌊ inRangeAndFilter? 3 (((225 , 225 , const ⊤ , (λ x → yes tt))) Vec.∷ ((161 , 161 , const ⊤ , (λ x → yes tt))) Vec.∷ (((184 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case225 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case225 c = ⌊ inRangeAndFilter? 3 (((225 , 225 , const ⊤ , (λ x → yes tt))) Vec.∷ ((163 , 183 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case226 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case226 c = ⌊ inRangeAndFilter? 3 (((225 , 225 , const ⊤ , (λ x → yes tt))) Vec.∷ ((186 , 186 , const ⊤ , (λ x → yes tt))) Vec.∷ (((156 , 159 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case227 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case227 c = ⌊ inRangeAndFilter? 3 (((225 , 225 , const ⊤ , (λ x → yes tt))) Vec.∷ ((189 , 189 , const ⊤ , (λ x → yes tt))) Vec.∷ (((152 , 152 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case228 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case228 c = ⌊ inRangeAndFilter? 3 (((225 , 225 , const ⊤ , (λ x → yes tt))) Vec.∷ ((189 , 189 , const ⊤ , (λ x → yes tt))) Vec.∷ (((154 , 154 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case229 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case229 c = ⌊ inRangeAndFilter? 3 (((225 , 225 , const ⊤ , (λ x → yes tt))) Vec.∷ ((189 , 189 , const ⊤ , (λ x → yes tt))) Vec.∷ (((156 , 156 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case230 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case230 c = ⌊ inRangeAndFilter? 3 (((225 , 225 , const ⊤ , (λ x → yes tt))) Vec.∷ ((191 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ (((156 , 156 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case231 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case231 c = ⌊ inRangeAndFilter? 3 (((225 , 225 , const ⊤ , (λ x → yes tt))) Vec.∷ ((189 , 189 , const ⊤ , (λ x → yes tt))) Vec.∷ (((158 , 158 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case232 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case232 c = ⌊ inRangeAndFilter? 3 (((225 , 225 , const ⊤ , (λ x → yes tt))) Vec.∷ ((189 , 189 , const ⊤ , (λ x → yes tt))) Vec.∷ (((190 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case233 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case233 c = ⌊ inRangeAndFilter? 3 (((225 , 225 , const ⊤ , (λ x → yes tt))) Vec.∷ ((190 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ (((181 , 181 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case234 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case234 c = ⌊ inRangeAndFilter? 3 (((225 , 225 , const ⊤ , (λ x → yes tt))) Vec.∷ ((191 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ (((133 , 133 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case235 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case235 c = ⌊ inRangeAndFilter? 3 (((225 , 225 , const ⊤ , (λ x → yes tt))) Vec.∷ ((191 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ (((148 , 149 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case236 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case236 c = ⌊ inRangeAndFilter? 3 (((225 , 225 , const ⊤ , (λ x → yes tt))) Vec.∷ ((191 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ (((176 , 177 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case237 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case237 c = ⌊ inRangeAndFilter? 3 (((226 , 226 , const ⊤ , (λ x → yes tt))) Vec.∷ ((129 , 129 , const ⊤ , (λ x → yes tt))) Vec.∷ (((147 , 150 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case238 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case238 c = ⌊ inRangeAndFilter? 3 (((226 , 226 , const ⊤ , (λ x → yes tt))) Vec.∷ ((129 , 129 , const ⊤ , (λ x → yes tt))) Vec.∷ (((152 , 158 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case239 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case239 c = ⌊ inRangeAndFilter? 3 (((226 , 226 , const ⊤ , (λ x → yes tt))) Vec.∷ ((129 , 129 , const ⊤ , (λ x → yes tt))) Vec.∷ (((164 , 169 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case240 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case240 c = ⌊ inRangeAndFilter? 3 (((226 , 226 , const ⊤ , (λ x → yes tt))) Vec.∷ ((129 , 129 , const ⊤ , (λ x → yes tt))) Vec.∷ (((178 , 179 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case241 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case241 c = ⌊ inRangeAndFilter? 3 (((226 , 226 , const ⊤ , (λ x → yes tt))) Vec.∷ ((130 , 130 , const ⊤ , (λ x → yes tt))) Vec.∷ (((143 , 159 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case242 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case242 c = ⌊ inRangeAndFilter? 3 (((226 , 226 , const ⊤ , (λ x → yes tt))) Vec.∷ ((130 , 130 , const ⊤ , (λ x → yes tt))) Vec.∷ (((178 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case243 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case243 c = ⌊ inRangeAndFilter? 3 (((226 , 226 , const ⊤ , (λ x → yes tt))) Vec.∷ ((131 , 131 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 143 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case244 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case244 c = ⌊ inRangeAndFilter? 3 (((226 , 226 , const ⊤ , (λ x → yes tt))) Vec.∷ ((159 , 159 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 143 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case245 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case245 c = ⌊ inRangeAndFilter? 3 (((226 , 226 , const ⊤ , (λ x → yes tt))) Vec.∷ ((131 , 131 , const ⊤ , (λ x → yes tt))) Vec.∷ (((171 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case246 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case246 c = ⌊ inRangeAndFilter? 3 (((226 , 226 , const ⊤ , (λ x → yes tt))) Vec.∷ ((132 , 132 , const ⊤ , (λ x → yes tt))) Vec.∷ (((187 , 188 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case247 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case247 c = ⌊ inRangeAndFilter? 3 (((226 , 226 , const ⊤ , (λ x → yes tt))) Vec.∷ ((133 , 133 , const ⊤ , (λ x → yes tt))) Vec.∷ (((140 , 146 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case248 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case248 c = ⌊ inRangeAndFilter? 3 (((226 , 226 , const ⊤ , (λ x → yes tt))) Vec.∷ ((134 , 134 , const ⊤ , (λ x → yes tt))) Vec.∷ (((132 , 143 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case249 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case249 c = ⌊ inRangeAndFilter? 3 (((226 , 226 , const ⊤ , (λ x → yes tt))) Vec.∷ ((143 , 143 , const ⊤ , (λ x → yes tt))) Vec.∷ (((143 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case250 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case250 c = ⌊ inRangeAndFilter? 3 (((226 , 226 , const ⊤ , (λ x → yes tt))) Vec.∷ ((144 , 144 , const ⊤ , (λ x → yes tt))) Vec.∷ (((167 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case251 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case251 c = ⌊ inRangeAndFilter? 3 (((226 , 226 , const ⊤ , (λ x → yes tt))) Vec.∷ ((145 , 145 , const ⊤ , (λ x → yes tt))) Vec.∷ (((139 , 159 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case252 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case252 c = ⌊ inRangeAndFilter? 3 (((226 , 226 , const ⊤ , (λ x → yes tt))) Vec.∷ ((147 , 147 , const ⊤ , (λ x → yes tt))) Vec.∷ (((191 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case253 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case253 c = ⌊ inRangeAndFilter? 3 (((226 , 226 , const ⊤ , (λ x → yes tt))) Vec.∷ ((158 , 158 , const ⊤ , (λ x → yes tt))) Vec.∷ (((191 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case254 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case254 c = ⌊ inRangeAndFilter? 3 (((226 , 226 , const ⊤ , (λ x → yes tt))) Vec.∷ ((152 , 152 , const ⊤ , (λ x → yes tt))) Vec.∷ (((148 , 149 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case255 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case255 c = ⌊ inRangeAndFilter? 3 (((226 , 226 , const ⊤ , (λ x → yes tt))) Vec.∷ ((152 , 152 , const ⊤ , (λ x → yes tt))) Vec.∷ (((152 , 152 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case256 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case256 c = ⌊ inRangeAndFilter? 3 (((226 , 226 , const ⊤ , (λ x → yes tt))) Vec.∷ ((153 , 153 , const ⊤ , (λ x → yes tt))) Vec.∷ (((190 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case257 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case257 c = ⌊ inRangeAndFilter? 3 (((226 , 226 , const ⊤ , (λ x → yes tt))) Vec.∷ ((154 , 154 , const ⊤ , (λ x → yes tt))) Vec.∷ (((138 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case258 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case258 c = ⌊ inRangeAndFilter? 3 (((226 , 226 , const ⊤ , (λ x → yes tt))) Vec.∷ ((155 , 155 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case259 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case259 c = ⌊ inRangeAndFilter? 3 (((226 , 226 , const ⊤ , (λ x → yes tt))) Vec.∷ ((172 , 185 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case260 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case260 c = ⌊ inRangeAndFilter? 3 (((226 , 226 , const ⊤ , (λ x → yes tt))) Vec.∷ ((156 , 156 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 128 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case261 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case261 c = ⌊ inRangeAndFilter? 3 (((226 , 226 , const ⊤ , (λ x → yes tt))) Vec.∷ ((156 , 156 , const ⊤ , (λ x → yes tt))) Vec.∷ (((133 , 133 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case262 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case262 c = ⌊ inRangeAndFilter? 3 (((226 , 226 , const ⊤ , (λ x → yes tt))) Vec.∷ ((156 , 156 , const ⊤ , (λ x → yes tt))) Vec.∷ (((138 , 139 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case263 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case263 c = ⌊ inRangeAndFilter? 3 (((226 , 226 , const ⊤ , (λ x → yes tt))) Vec.∷ ((156 , 156 , const ⊤ , (λ x → yes tt))) Vec.∷ (((168 , 168 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case264 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case264 c = ⌊ inRangeAndFilter? 3 (((226 , 226 , const ⊤ , (λ x → yes tt))) Vec.∷ ((157 , 157 , const ⊤ , (λ x → yes tt))) Vec.∷ (((140 , 140 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case265 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case265 c = ⌊ inRangeAndFilter? 3 (((226 , 226 , const ⊤ , (λ x → yes tt))) Vec.∷ ((157 , 157 , const ⊤ , (λ x → yes tt))) Vec.∷ (((142 , 142 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case266 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case266 c = ⌊ inRangeAndFilter? 3 (((226 , 226 , const ⊤ , (λ x → yes tt))) Vec.∷ ((157 , 157 , const ⊤ , (λ x → yes tt))) Vec.∷ (((147 , 149 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case267 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case267 c = ⌊ inRangeAndFilter? 3 (((226 , 226 , const ⊤ , (λ x → yes tt))) Vec.∷ ((157 , 157 , const ⊤ , (λ x → yes tt))) Vec.∷ (((151 , 151 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case268 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case268 c = ⌊ inRangeAndFilter? 3 (((226 , 226 , const ⊤ , (λ x → yes tt))) Vec.∷ ((157 , 157 , const ⊤ , (λ x → yes tt))) Vec.∷ (((159 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case269 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case269 c = ⌊ inRangeAndFilter? 3 (((226 , 226 , const ⊤ , (λ x → yes tt))) Vec.∷ ((158 , 158 , const ⊤ , (λ x → yes tt))) Vec.∷ (((149 , 151 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case270 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case270 c = ⌊ inRangeAndFilter? 3 (((226 , 226 , const ⊤ , (λ x → yes tt))) Vec.∷ ((158 , 158 , const ⊤ , (λ x → yes tt))) Vec.∷ (((176 , 176 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case271 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case271 c = ⌊ inRangeAndFilter? 3 (((226 , 226 , const ⊤ , (λ x → yes tt))) Vec.∷ ((159 , 159 , const ⊤ , (λ x → yes tt))) Vec.∷ (((172 , 175 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case272 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case272 c = ⌊ inRangeAndFilter? 3 (((226 , 226 , const ⊤ , (λ x → yes tt))) Vec.∷ ((186 , 186 , const ⊤ , (λ x → yes tt))) Vec.∷ (((154 , 154 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case273 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case273 c = ⌊ inRangeAndFilter? 3 (((226 , 226 , const ⊤ , (λ x → yes tt))) Vec.∷ ((187 , 187 , const ⊤ , (λ x → yes tt))) Vec.∷ (((180 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case274 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case274 c = ⌊ inRangeAndFilter? 3 (((226 , 226 , const ⊤ , (λ x → yes tt))) Vec.∷ ((191 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ (((150 , 175 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case275 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case275 c = ⌊ inRangeAndFilter? 3 (((226 , 226 , const ⊤ , (λ x → yes tt))) Vec.∷ ((191 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ (((188 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case276 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case276 c = ⌊ inRangeAndFilter? 3 (((227 , 227 , const ⊤ , (λ x → yes tt))) Vec.∷ ((129 , 129 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 128 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case277 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case277 c = ⌊ inRangeAndFilter? 3 (((227 , 227 , const ⊤ , (λ x → yes tt))) Vec.∷ ((130 , 130 , const ⊤ , (λ x → yes tt))) Vec.∷ (((151 , 152 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case278 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case278 c = ⌊ inRangeAndFilter? 3 (((227 , 227 , const ⊤ , (λ x → yes tt))) Vec.∷ ((132 , 132 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 132 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case279 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case279 c = ⌊ inRangeAndFilter? 3 (((227 , 227 , const ⊤ , (λ x → yes tt))) Vec.∷ ((132 , 132 , const ⊤ , (λ x → yes tt))) Vec.∷ (((173 , 176 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case280 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case280 c = ⌊ inRangeAndFilter? 3 (((227 , 227 , const ⊤ , (λ x → yes tt))) Vec.∷ ((134 , 134 , const ⊤ , (λ x → yes tt))) Vec.∷ (((143 , 143 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case281 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case281 c = ⌊ inRangeAndFilter? 3 (((227 , 227 , const ⊤ , (λ x → yes tt))) Vec.∷ ((134 , 134 , const ⊤ , (λ x → yes tt))) Vec.∷ (((184 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case282 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case282 c = ⌊ inRangeAndFilter? 3 (((227 , 227 , const ⊤ , (λ x → yes tt))) Vec.∷ ((135 , 135 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 175 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case283 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case283 c = ⌊ inRangeAndFilter? 3 (((227 , 227 , const ⊤ , (λ x → yes tt))) Vec.∷ ((136 , 136 , const ⊤ , (λ x → yes tt))) Vec.∷ (((157 , 159 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case284 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case284 c = ⌊ inRangeAndFilter? 3 (((227 , 227 , const ⊤ , (λ x → yes tt))) Vec.∷ ((137 , 137 , const ⊤ , (λ x → yes tt))) Vec.∷ (((132 , 144 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case285 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case285 c = ⌊ inRangeAndFilter? 3 (((227 , 227 , const ⊤ , (λ x → yes tt))) Vec.∷ ((137 , 137 , const ⊤ , (λ x → yes tt))) Vec.∷ (((188 , 190 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case286 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case286 c = ⌊ inRangeAndFilter? 3 (((227 , 227 , const ⊤ , (λ x → yes tt))) Vec.∷ ((139 , 139 , const ⊤ , (λ x → yes tt))) Vec.∷ (((140 , 143 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case287 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case287 c = ⌊ inRangeAndFilter? 3 (((227 , 227 , const ⊤ , (λ x → yes tt))) Vec.∷ ((139 , 139 , const ⊤ , (λ x → yes tt))) Vec.∷ (((191 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case288 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case288 c = ⌊ inRangeAndFilter? 3 (((227 , 227 , const ⊤ , (λ x → yes tt))) Vec.∷ ((143 , 143 , const ⊤ , (λ x → yes tt))) Vec.∷ (((191 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case289 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case289 c = ⌊ inRangeAndFilter? 3 (((227 , 227 , const ⊤ , (λ x → yes tt))) Vec.∷ ((141 , 141 , const ⊤ , (λ x → yes tt))) Vec.∷ (((183 , 186 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case290 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case290 c = ⌊ inRangeAndFilter? 3 (((227 , 227 , const ⊤ , (λ x → yes tt))) Vec.∷ ((143 , 143 , const ⊤ , (λ x → yes tt))) Vec.∷ (((158 , 159 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case291 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case291 c = ⌊ inRangeAndFilter? 3 (((228 , 228 , const ⊤ , (λ x → yes tt))) Vec.∷ ((182 , 182 , const ⊤ , (λ x → yes tt))) Vec.∷ (((182 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case292 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case292 c = ⌊ inRangeAndFilter? 3 (((228 , 228 , const ⊤ , (λ x → yes tt))) Vec.∷ ((183 , 183 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case293 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case293 c = ⌊ inRangeAndFilter? 3 (((233 , 233 , const ⊤ , (λ x → yes tt))) Vec.∷ ((190 , 190 , const ⊤ , (λ x → yes tt))) Vec.∷ (((166 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case294 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case294 c = ⌊ inRangeAndFilter? 3 (((233 , 233 , const ⊤ , (λ x → yes tt))) Vec.∷ ((191 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case295 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case295 c = ⌊ inRangeAndFilter? 3 (((234 , 234 , const ⊤ , (λ x → yes tt))) Vec.∷ ((146 , 146 , const ⊤ , (λ x → yes tt))) Vec.∷ (((141 , 143 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case296 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case296 c = ⌊ inRangeAndFilter? 3 (((234 , 234 , const ⊤ , (λ x → yes tt))) Vec.∷ ((147 , 147 , const ⊤ , (λ x → yes tt))) Vec.∷ (((135 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case297 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case297 c = ⌊ inRangeAndFilter? 3 (((234 , 234 , const ⊤ , (λ x → yes tt))) Vec.∷ ((148 , 175 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case298 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case298 c = ⌊ inRangeAndFilter? 3 (((237 , 237 , const ⊤ , (λ x → yes tt))) Vec.∷ ((158 , 158 , const ⊤ , (λ x → yes tt))) Vec.∷ (((164 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case299 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case299 c = ⌊ inRangeAndFilter? 3 (((237 , 237 , const ⊤ , (λ x → yes tt))) Vec.∷ ((159 , 159 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case300 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case300 c = ⌊ inRangeAndFilter? 3 (((239 , 239 , const ⊤ , (λ x → yes tt))) Vec.∷ ((168 , 168 , const ⊤ , (λ x → yes tt))) Vec.∷ (((174 , 175 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case301 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case301 c = ⌊ inRangeAndFilter? 3 (((239 , 239 , const ⊤ , (λ x → yes tt))) Vec.∷ ((169 , 169 , const ⊤ , (λ x → yes tt))) Vec.∷ (((171 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case302 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case302 c = ⌊ inRangeAndFilter? 3 (((239 , 239 , const ⊤ , (λ x → yes tt))) Vec.∷ ((170 , 171 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case303 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case303 c = ⌊ inRangeAndFilter? 3 (((239 , 239 , const ⊤ , (λ x → yes tt))) Vec.∷ ((172 , 172 , const ⊤ , (λ x → yes tt))) Vec.∷ (((135 , 146 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case304 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case304 c = ⌊ inRangeAndFilter? 3 (((239 , 239 , const ⊤ , (λ x → yes tt))) Vec.∷ ((172 , 172 , const ⊤ , (λ x → yes tt))) Vec.∷ (((152 , 156 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case305 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case305 c = ⌊ inRangeAndFilter? 3 (((239 , 239 , const ⊤ , (λ x → yes tt))) Vec.∷ ((172 , 172 , const ⊤ , (λ x → yes tt))) Vec.∷ (((183 , 183 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case306 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case306 c = ⌊ inRangeAndFilter? 3 (((239 , 239 , const ⊤ , (λ x → yes tt))) Vec.∷ ((172 , 172 , const ⊤ , (λ x → yes tt))) Vec.∷ (((189 , 189 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case307 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case307 c = ⌊ inRangeAndFilter? 3 (((239 , 239 , const ⊤ , (λ x → yes tt))) Vec.∷ ((172 , 172 , const ⊤ , (λ x → yes tt))) Vec.∷ (((191 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case308 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case308 c = ⌊ inRangeAndFilter? 3 (((239 , 239 , const ⊤ , (λ x → yes tt))) Vec.∷ ((190 , 190 , const ⊤ , (λ x → yes tt))) Vec.∷ (((191 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case309 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case309 c = ⌊ inRangeAndFilter? 3 (((239 , 239 , const ⊤ , (λ x → yes tt))) Vec.∷ ((173 , 173 , const ⊤ , (λ x → yes tt))) Vec.∷ (((130 , 130 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case310 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case310 c = ⌊ inRangeAndFilter? 3 (((239 , 239 , const ⊤ , (λ x → yes tt))) Vec.∷ ((173 , 173 , const ⊤ , (λ x → yes tt))) Vec.∷ (((133 , 133 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case311 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case311 c = ⌊ inRangeAndFilter? 3 (((239 , 239 , const ⊤ , (λ x → yes tt))) Vec.∷ ((174 , 174 , const ⊤ , (λ x → yes tt))) Vec.∷ (((178 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case312 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case312 c = ⌊ inRangeAndFilter? 3 (((239 , 239 , const ⊤ , (λ x → yes tt))) Vec.∷ ((175 , 175 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 146 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case313 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case313 c = ⌊ inRangeAndFilter? 3 (((239 , 239 , const ⊤ , (λ x → yes tt))) Vec.∷ ((181 , 181 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 143 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case314 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case314 c = ⌊ inRangeAndFilter? 3 (((239 , 239 , const ⊤ , (λ x → yes tt))) Vec.∷ ((182 , 182 , const ⊤ , (λ x → yes tt))) Vec.∷ (((144 , 145 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case315 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case315 c = ⌊ inRangeAndFilter? 3 (((239 , 239 , const ⊤ , (λ x → yes tt))) Vec.∷ ((191 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ (((144 , 145 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case316 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case316 c = ⌊ inRangeAndFilter? 3 (((239 , 239 , const ⊤ , (λ x → yes tt))) Vec.∷ ((183 , 183 , const ⊤ , (λ x → yes tt))) Vec.∷ (((136 , 143 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case317 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case317 c = ⌊ inRangeAndFilter? 3 (((239 , 239 , const ⊤ , (λ x → yes tt))) Vec.∷ ((183 , 183 , const ⊤ , (λ x → yes tt))) Vec.∷ (((189 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case318 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case318 c = ⌊ inRangeAndFilter? 3 (((239 , 239 , const ⊤ , (λ x → yes tt))) Vec.∷ ((184 , 184 , const ⊤ , (λ x → yes tt))) Vec.∷ (((144 , 159 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case319 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case319 c = ⌊ inRangeAndFilter? 3 (((239 , 239 , const ⊤ , (λ x → yes tt))) Vec.∷ ((184 , 184 , const ⊤ , (λ x → yes tt))) Vec.∷ (((164 , 175 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case320 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case320 c = ⌊ inRangeAndFilter? 3 (((239 , 239 , const ⊤ , (λ x → yes tt))) Vec.∷ ((185 , 185 , const ⊤ , (λ x → yes tt))) Vec.∷ (((135 , 136 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case321 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case321 c = ⌊ inRangeAndFilter? 3 (((239 , 239 , const ⊤ , (λ x → yes tt))) Vec.∷ ((185 , 185 , const ⊤ , (λ x → yes tt))) Vec.∷ (((147 , 147 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case322 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case322 c = ⌊ inRangeAndFilter? 3 (((239 , 239 , const ⊤ , (λ x → yes tt))) Vec.∷ ((185 , 185 , const ⊤ , (λ x → yes tt))) Vec.∷ (((167 , 167 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case323 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case323 c = ⌊ inRangeAndFilter? 3 (((239 , 239 , const ⊤ , (λ x → yes tt))) Vec.∷ ((191 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ (((167 , 167 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case324 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case324 c = ⌊ inRangeAndFilter? 3 (((239 , 239 , const ⊤ , (λ x → yes tt))) Vec.∷ ((185 , 185 , const ⊤ , (λ x → yes tt))) Vec.∷ (((172 , 175 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case325 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case325 c = ⌊ inRangeAndFilter? 3 (((239 , 239 , const ⊤ , (λ x → yes tt))) Vec.∷ ((185 , 185 , const ⊤ , (λ x → yes tt))) Vec.∷ (((181 , 181 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case326 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case326 c = ⌊ inRangeAndFilter? 3 (((239 , 239 , const ⊤ , (λ x → yes tt))) Vec.∷ ((187 , 187 , const ⊤ , (λ x → yes tt))) Vec.∷ (((189 , 190 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case327 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case327 c = ⌊ inRangeAndFilter? 3 (((239 , 239 , const ⊤ , (λ x → yes tt))) Vec.∷ ((188 , 188 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 128 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case328 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case328 c = ⌊ inRangeAndFilter? 3 (((239 , 239 , const ⊤ , (λ x → yes tt))) Vec.∷ ((191 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 129 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case329 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case329 c = ⌊ inRangeAndFilter? 3 (((239 , 239 , const ⊤ , (λ x → yes tt))) Vec.∷ ((191 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ (((136 , 137 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case330 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case330 c = ⌊ inRangeAndFilter? 3 (((239 , 239 , const ⊤ , (λ x → yes tt))) Vec.∷ ((191 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ (((152 , 153 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case331 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case331 c = ⌊ inRangeAndFilter? 3 (((239 , 239 , const ⊤ , (λ x → yes tt))) Vec.∷ ((191 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ (((157 , 159 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case332 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case332 c = ⌊ inRangeAndFilter? 3 (((239 , 239 , const ⊤ , (λ x → yes tt))) Vec.∷ ((191 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ (((175 , 184 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    check : ∀ {@0 bs} → UTF8Char bs → Bool
    check x = or (List.map (λ f → f x) fs)
      where
      fs : List (∀ {@0 bs} → UTF8Char bs → Bool)
      fs = case1 ∷ case2 ∷ case3 ∷ case4 ∷ case5 ∷ case6 ∷ case7 ∷ case8 ∷ case9 ∷ case10 ∷ case11 ∷ case12 ∷ case13 ∷ case14 ∷ case15 ∷ case16 ∷ case17 ∷ case18 ∷ case19 ∷ case20 ∷ case21 ∷ case22 ∷ case23 ∷ case24 ∷ case25 ∷ case26 ∷ case27 ∷ case28 ∷ case29 ∷ case30 ∷ case31 ∷ case32 ∷ case33 ∷ case34 ∷ case35 ∷ case36 ∷ case37 ∷ case38 ∷ case39 ∷ case40 ∷ case41 ∷ case42 ∷ case43 ∷ case44 ∷ case45 ∷ case46 ∷ case47 ∷ case48 ∷ case49 ∷ case50 ∷ case51 ∷ case52 ∷ case53 ∷ case54 ∷ case55 ∷ case56 ∷ case57 ∷ case58 ∷ case59 ∷ case60 ∷ case61 ∷ case62 ∷ case63 ∷ case64 ∷ case65 ∷ case66 ∷ case67 ∷ case68 ∷ case69 ∷ case70 ∷ case71 ∷ case72 ∷ case73 ∷ case74 ∷ case75 ∷ case76 ∷ case77 ∷ case78 ∷ case79 ∷ case80 ∷ case81 ∷ case82 ∷ case83 ∷ case84 ∷ case85 ∷ case86 ∷ case87 ∷ case88 ∷ case89 ∷ case90 ∷ case91 ∷ case92 ∷ case93 ∷ case94 ∷ case95 ∷ case96 ∷ case97 ∷ case98 ∷ case99 ∷ case100 ∷ case101 ∷ case102 ∷ case103 ∷ case104 ∷ case105 ∷ case106 ∷ case107 ∷ case108 ∷ case109 ∷ case110 ∷ case111 ∷ case112 ∷ case113 ∷ case114 ∷ case115 ∷ case116 ∷ case117 ∷ case118 ∷ case119 ∷ case120 ∷ case121 ∷ case122 ∷ case123 ∷ case124 ∷ case125 ∷ case126 ∷ case127 ∷ case128 ∷ case129 ∷ case130 ∷ case131 ∷ case132 ∷ case133 ∷ case134 ∷ case135 ∷ case136 ∷ case137 ∷ case138 ∷ case139 ∷ case140 ∷ case141 ∷ case142 ∷ case143 ∷ case144 ∷ case145 ∷ case146 ∷ case147 ∷ case148 ∷ case149 ∷ case150 ∷ case151 ∷ case152 ∷ case153 ∷ case154 ∷ case155 ∷ case156 ∷ case157 ∷ case158 ∷ case159 ∷ case160 ∷ case161 ∷ case162 ∷ case163 ∷ case164 ∷ case165 ∷ case166 ∷ case167 ∷ case168 ∷ case169 ∷ case170 ∷ case171 ∷ case172 ∷ case173 ∷ case174 ∷ case175 ∷ case176 ∷ case177 ∷ case178 ∷ case179 ∷ case180 ∷ case181 ∷ case182 ∷ case183 ∷ case184 ∷ case185 ∷ case186 ∷ case187 ∷ case188 ∷ case189 ∷ case190 ∷ case191 ∷ case192 ∷ case193 ∷ case194 ∷ case195 ∷ case196 ∷ case197 ∷ case198 ∷ case199 ∷ case200 ∷ case201 ∷ case202 ∷ case203 ∷ case204 ∷ case205 ∷ case206 ∷ case207 ∷ case208 ∷ case209 ∷ case210 ∷ case211 ∷ case212 ∷ case213 ∷ case214 ∷ case215 ∷ case216 ∷ case217 ∷ case218 ∷ case219 ∷ case220 ∷ case221 ∷ case222 ∷ case223 ∷ case224 ∷ case225 ∷ case226 ∷ case227 ∷ case228 ∷ case229 ∷ case230 ∷ case231 ∷ case232 ∷ case233 ∷ case234 ∷ case235 ∷ case236 ∷ case237 ∷ case238 ∷ case239 ∷ case240 ∷ case241 ∷ case242 ∷ case243 ∷ case244 ∷ case245 ∷ case246 ∷ case247 ∷ case248 ∷ case249 ∷ case250 ∷ case251 ∷ case252 ∷ case253 ∷ case254 ∷ case255 ∷ case256 ∷ case257 ∷ case258 ∷ case259 ∷ case260 ∷ case261 ∷ case262 ∷ case263 ∷ case264 ∷ case265 ∷ case266 ∷ case267 ∷ case268 ∷ case269 ∷ case270 ∷ case271 ∷ case272 ∷ case273 ∷ case274 ∷ case275 ∷ case276 ∷ case277 ∷ case278 ∷ case279 ∷ case280 ∷ case281 ∷ case282 ∷ case283 ∷ case284 ∷ case285 ∷ case286 ∷ case287 ∷ case288 ∷ case289 ∷ case290 ∷ case291 ∷ case292 ∷ case293 ∷ case294 ∷ case295 ∷ case296 ∷ case297 ∷ case298 ∷ case299 ∷ case300 ∷ case301 ∷ case302 ∷ case303 ∷ case304 ∷ case305 ∷ case306 ∷ case307 ∷ case308 ∷ case309 ∷ case310 ∷ case311 ∷ case312 ∷ case313 ∷ case314 ∷ case315 ∷ case316 ∷ case317 ∷ case318 ∷ case319 ∷ case320 ∷ case321 ∷ case322 ∷ case323 ∷ case324 ∷ case325 ∷ case326 ∷ case327 ∷ case328 ∷ case329 ∷ case330 ∷ case331 ∷ case332 ∷ []

  module CasesForUTF84 where
    case1 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case1 c = ⌊ inRangeAndFilter? 4 (((240 , 240 , const ⊤ , (λ x → yes tt))) Vec.∷ (((144 , 144 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 139 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case2 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case2 c = ⌊ inRangeAndFilter? 4 (((240 , 240 , const ⊤ , (λ x → yes tt))) Vec.∷ (((144 , 144 , const ⊤ , (λ x → yes tt))) Vec.∷ (((142 , 143 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case3 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case3 c = ⌊ inRangeAndFilter? 4 (((240 , 240 , const ⊤ , (λ x → yes tt))) Vec.∷ (((144 , 144 , const ⊤ , (λ x → yes tt))) Vec.∷ (((146 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case4 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case4 c = ⌊ inRangeAndFilter? 4 (((240 , 240 , const ⊤ , (λ x → yes tt))) Vec.∷ (((144 , 144 , const ⊤ , (λ x → yes tt))) Vec.∷ (((140 , 140 , const ⊤ , (λ x → yes tt))) Vec.∷ (((159 , 159 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case5 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case5 c = ⌊ inRangeAndFilter? 4 (((240 , 240 , const ⊤ , (λ x → yes tt))) Vec.∷ (((144 , 144 , const ⊤ , (λ x → yes tt))) Vec.∷ (((140 , 140 , const ⊤ , (λ x → yes tt))) Vec.∷ (((164 , 175 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case6 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case6 c = ⌊ inRangeAndFilter? 4 (((240 , 240 , const ⊤ , (λ x → yes tt))) Vec.∷ (((144 , 144 , const ⊤ , (λ x → yes tt))) Vec.∷ (((141 , 141 , const ⊤ , (λ x → yes tt))) Vec.∷ (((139 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case7 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case7 c = ⌊ inRangeAndFilter? 4 (((240 , 240 , const ⊤ , (λ x → yes tt))) Vec.∷ (((144 , 144 , const ⊤ , (λ x → yes tt))) Vec.∷ (((144 , 144 , const ⊤ , (λ x → yes tt))) Vec.∷ (((166 , 167 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case8 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case8 c = ⌊ inRangeAndFilter? 4 (((240 , 240 , const ⊤ , (λ x → yes tt))) Vec.∷ (((144 , 144 , const ⊤ , (λ x → yes tt))) Vec.∷ (((145 , 145 , const ⊤ , (λ x → yes tt))) Vec.∷ (((142 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case9 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case9 c = ⌊ inRangeAndFilter? 4 (((240 , 240 , const ⊤ , (λ x → yes tt))) Vec.∷ (((145 , 156 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case10 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case10 c = ⌊ inRangeAndFilter? 4 (((240 , 240 , const ⊤ , (λ x → yes tt))) Vec.∷ (((158 , 158 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case11 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case11 c = ⌊ inRangeAndFilter? 4 (((240 , 240 , const ⊤ , (λ x → yes tt))) Vec.∷ (((171 , 174 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case12 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case12 c = ⌊ inRangeAndFilter? 4 (((240 , 242 , const ⊤ , (λ x → yes tt))) Vec.∷ (((176 , 190 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case13 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case13 c = ⌊ inRangeAndFilter? 4 (((240 , 240 , const ⊤ , (λ x → yes tt))) Vec.∷ (((157 , 157 , const ⊤ , (λ x → yes tt))) Vec.∷ (((131 , 131 , const ⊤ , (λ x → yes tt))) Vec.∷ (((182 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case14 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case14 c = ⌊ inRangeAndFilter? 4 (((240 , 240 , const ⊤ , (λ x → yes tt))) Vec.∷ (((157 , 157 , const ⊤ , (λ x → yes tt))) Vec.∷ (((132 , 132 , const ⊤ , (λ x → yes tt))) Vec.∷ (((167 , 169 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case15 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case15 c = ⌊ inRangeAndFilter? 4 (((240 , 240 , const ⊤ , (λ x → yes tt))) Vec.∷ (((157 , 157 , const ⊤ , (λ x → yes tt))) Vec.∷ (((135 , 135 , const ⊤ , (λ x → yes tt))) Vec.∷ (((158 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case16 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case16 c = ⌊ inRangeAndFilter? 4 (((240 , 240 , const ⊤ , (λ x → yes tt))) Vec.∷ (((157 , 157 , const ⊤ , (λ x → yes tt))) Vec.∷ (((136 , 143 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case17 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case17 c = ⌊ inRangeAndFilter? 4 (((240 , 240 , const ⊤ , (λ x → yes tt))) Vec.∷ (((157 , 157 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case18 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case18 c = ⌊ inRangeAndFilter? 4 (((240 , 240 , const ⊤ , (λ x → yes tt))) Vec.∷ (((157 , 157 , const ⊤ , (λ x → yes tt))) Vec.∷ (((145 , 145 , const ⊤ , (λ x → yes tt))) Vec.∷ (((149 , 149 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case19 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case19 c = ⌊ inRangeAndFilter? 4 (((240 , 240 , const ⊤ , (λ x → yes tt))) Vec.∷ (((157 , 157 , const ⊤ , (λ x → yes tt))) Vec.∷ (((148 , 148 , const ⊤ , (λ x → yes tt))) Vec.∷ (((149 , 149 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case20 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case20 c = ⌊ inRangeAndFilter? 4 (((240 , 240 , const ⊤ , (λ x → yes tt))) Vec.∷ (((157 , 157 , const ⊤ , (λ x → yes tt))) Vec.∷ (((146 , 146 , const ⊤ , (λ x → yes tt))) Vec.∷ (((157 , 157 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case21 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case21 c = ⌊ inRangeAndFilter? 4 (((240 , 240 , const ⊤ , (λ x → yes tt))) Vec.∷ (((157 , 157 , const ⊤ , (λ x → yes tt))) Vec.∷ (((148 , 148 , const ⊤ , (λ x → yes tt))) Vec.∷ (((157 , 157 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case22 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case22 c = ⌊ inRangeAndFilter? 4 (((240 , 240 , const ⊤ , (λ x → yes tt))) Vec.∷ (((157 , 157 , const ⊤ , (λ x → yes tt))) Vec.∷ (((146 , 146 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 161 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case23 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case23 c = ⌊ inRangeAndFilter? 4 (((240 , 240 , const ⊤ , (λ x → yes tt))) Vec.∷ (((157 , 157 , const ⊤ , (λ x → yes tt))) Vec.∷ (((146 , 146 , const ⊤ , (λ x → yes tt))) Vec.∷ (((163 , 164 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case24 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case24 c = ⌊ inRangeAndFilter? 4 (((240 , 240 , const ⊤ , (λ x → yes tt))) Vec.∷ (((157 , 157 , const ⊤ , (λ x → yes tt))) Vec.∷ (((146 , 146 , const ⊤ , (λ x → yes tt))) Vec.∷ (((167 , 168 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case25 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case25 c = ⌊ inRangeAndFilter? 4 (((240 , 240 , const ⊤ , (λ x → yes tt))) Vec.∷ (((157 , 157 , const ⊤ , (λ x → yes tt))) Vec.∷ (((146 , 146 , const ⊤ , (λ x → yes tt))) Vec.∷ (((173 , 173 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case26 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case26 c = ⌊ inRangeAndFilter? 4 (((240 , 240 , const ⊤ , (λ x → yes tt))) Vec.∷ (((157 , 157 , const ⊤ , (λ x → yes tt))) Vec.∷ (((146 , 146 , const ⊤ , (λ x → yes tt))) Vec.∷ (((186 , 186 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case27 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case27 c = ⌊ inRangeAndFilter? 4 (((240 , 240 , const ⊤ , (λ x → yes tt))) Vec.∷ (((157 , 157 , const ⊤ , (λ x → yes tt))) Vec.∷ (((148 , 148 , const ⊤ , (λ x → yes tt))) Vec.∷ (((186 , 186 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case28 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case28 c = ⌊ inRangeAndFilter? 4 (((240 , 240 , const ⊤ , (λ x → yes tt))) Vec.∷ (((157 , 157 , const ⊤ , (λ x → yes tt))) Vec.∷ (((146 , 146 , const ⊤ , (λ x → yes tt))) Vec.∷ (((188 , 188 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case29 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case29 c = ⌊ inRangeAndFilter? 4 (((240 , 240 , const ⊤ , (λ x → yes tt))) Vec.∷ (((157 , 157 , const ⊤ , (λ x → yes tt))) Vec.∷ (((147 , 147 , const ⊤ , (λ x → yes tt))) Vec.∷ (((129 , 129 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case30 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case30 c = ⌊ inRangeAndFilter? 4 (((240 , 240 , const ⊤ , (λ x → yes tt))) Vec.∷ (((157 , 157 , const ⊤ , (λ x → yes tt))) Vec.∷ (((147 , 147 , const ⊤ , (λ x → yes tt))) Vec.∷ (((132 , 132 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case31 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case31 c = ⌊ inRangeAndFilter? 4 (((240 , 240 , const ⊤ , (λ x → yes tt))) Vec.∷ (((157 , 157 , const ⊤ , (λ x → yes tt))) Vec.∷ (((148 , 148 , const ⊤ , (λ x → yes tt))) Vec.∷ (((134 , 134 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case32 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case32 c = ⌊ inRangeAndFilter? 4 (((240 , 240 , const ⊤ , (λ x → yes tt))) Vec.∷ (((157 , 157 , const ⊤ , (λ x → yes tt))) Vec.∷ (((148 , 148 , const ⊤ , (λ x → yes tt))) Vec.∷ (((139 , 140 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case33 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case33 c = ⌊ inRangeAndFilter? 4 (((240 , 240 , const ⊤ , (λ x → yes tt))) Vec.∷ (((157 , 157 , const ⊤ , (λ x → yes tt))) Vec.∷ (((148 , 148 , const ⊤ , (λ x → yes tt))) Vec.∷ (((191 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case34 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case34 c = ⌊ inRangeAndFilter? 4 (((240 , 240 , const ⊤ , (λ x → yes tt))) Vec.∷ (((157 , 157 , const ⊤ , (λ x → yes tt))) Vec.∷ (((149 , 149 , const ⊤ , (λ x → yes tt))) Vec.∷ (((133 , 133 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case35 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case35 c = ⌊ inRangeAndFilter? 4 (((240 , 240 , const ⊤ , (λ x → yes tt))) Vec.∷ (((157 , 157 , const ⊤ , (λ x → yes tt))) Vec.∷ (((149 , 149 , const ⊤ , (λ x → yes tt))) Vec.∷ (((135 , 137 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case36 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case36 c = ⌊ inRangeAndFilter? 4 (((240 , 240 , const ⊤ , (λ x → yes tt))) Vec.∷ (((157 , 157 , const ⊤ , (λ x → yes tt))) Vec.∷ (((149 , 149 , const ⊤ , (λ x → yes tt))) Vec.∷ (((145 , 145 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case37 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case37 c = ⌊ inRangeAndFilter? 4 (((240 , 240 , const ⊤ , (λ x → yes tt))) Vec.∷ (((157 , 157 , const ⊤ , (λ x → yes tt))) Vec.∷ (((154 , 154 , const ⊤ , (λ x → yes tt))) Vec.∷ (((164 , 167 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case38 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case38 c = ⌊ inRangeAndFilter? 4 (((240 , 240 , const ⊤ , (λ x → yes tt))) Vec.∷ (((157 , 157 , const ⊤ , (λ x → yes tt))) Vec.∷ (((159 , 159 , const ⊤ , (λ x → yes tt))) Vec.∷ (((138 , 141 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case39 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case39 c = ⌊ inRangeAndFilter? 4 (((240 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((159 , 159 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 190 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case40 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case40 c = ⌊ inRangeAndFilter? 4 (((240 , 242 , const ⊤ , (λ x → yes tt))) Vec.∷ (((191 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 190 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case41 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case41 c = ⌊ inRangeAndFilter? 4 (((240 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((159 , 159 , const ⊤ , (λ x → yes tt))) Vec.∷ (((191 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 189 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case42 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case42 c = ⌊ inRangeAndFilter? 4 (((240 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((175 , 175 , const ⊤ , (λ x → yes tt))) Vec.∷ (((191 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 189 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case43 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case43 c = ⌊ inRangeAndFilter? 4 (((240 , 242 , const ⊤ , (λ x → yes tt))) Vec.∷ (((191 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ (((191 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 189 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case44 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case44 c = ⌊ inRangeAndFilter? 4 (((240 , 240 , const ⊤ , (λ x → yes tt))) Vec.∷ (((170 , 170 , const ⊤ , (λ x → yes tt))) Vec.∷ (((155 , 155 , const ⊤ , (λ x → yes tt))) Vec.∷ (((151 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case45 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case45 c = ⌊ inRangeAndFilter? 4 (((240 , 240 , const ⊤ , (λ x → yes tt))) Vec.∷ (((170 , 170 , const ⊤ , (λ x → yes tt))) Vec.∷ (((156 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case46 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case46 c = ⌊ inRangeAndFilter? 4 (((240 , 240 , const ⊤ , (λ x → yes tt))) Vec.∷ (((175 , 175 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 159 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case47 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case47 c = ⌊ inRangeAndFilter? 4 (((240 , 240 , const ⊤ , (λ x → yes tt))) Vec.∷ (((175 , 175 , const ⊤ , (λ x → yes tt))) Vec.∷ (((169 , 190 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case48 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case48 c = ⌊ inRangeAndFilter? 4 (((240 , 240 , const ⊤ , (λ x → yes tt))) Vec.∷ (((175 , 175 , const ⊤ , (λ x → yes tt))) Vec.∷ (((168 , 168 , const ⊤ , (λ x → yes tt))) Vec.∷ (((158 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case49 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case49 c = ⌊ inRangeAndFilter? 4 (((241 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 142 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case50 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case50 c = ⌊ inRangeAndFilter? 4 (((241 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((144 , 158 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case51 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case51 c = ⌊ inRangeAndFilter? 4 (((241 , 242 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 174 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case52 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case52 c = ⌊ inRangeAndFilter? 4 (((241 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((143 , 143 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 190 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case53 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case53 c = ⌊ inRangeAndFilter? 4 (((241 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((175 , 175 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 190 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case54 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case54 c = ⌊ inRangeAndFilter? 4 (((241 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((143 , 143 , const ⊤ , (λ x → yes tt))) Vec.∷ (((191 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 189 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case55 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case55 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((161 , 174 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case56 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case56 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 128 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 128 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case57 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case57 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 128 , const ⊤ , (λ x → yes tt))) Vec.∷ (((130 , 159 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case58 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case58 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((130 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    check : ∀ {@0 bs} → UTF8Char bs → Bool
    check x = or (List.map (λ f → f x) fs)
      where
      fs : List (∀ {@0 bs} → UTF8Char bs → Bool)
      fs = case1 ∷ case2 ∷ case3 ∷ case4 ∷ case5 ∷ case6 ∷ case7 ∷ case8 ∷ case9 ∷ case10 ∷ case11 ∷ case12 ∷ case13 ∷ case14 ∷ case15 ∷ case16 ∷ case17 ∷ case18 ∷ case19 ∷ case20 ∷ case21 ∷ case22 ∷ case23 ∷ case24 ∷ case25 ∷ case26 ∷ case27 ∷ case28 ∷ case29 ∷ case30 ∷ case31 ∷ case32 ∷ case33 ∷ case34 ∷ case35 ∷ case36 ∷ case37 ∷ case38 ∷ case39 ∷ case40 ∷ case41 ∷ case42 ∷ case43 ∷ case44 ∷ case45 ∷ case46 ∷ case47 ∷ case48 ∷ case49 ∷ case50 ∷ case51 ∷ case52 ∷ case53 ∷ case54 ∷ case55 ∷ case56 ∷ case57 ∷ case58 ∷ []


checkProhibitUTF8Char : ∀ {@0 bs} → UTF8Char bs → Bool
checkProhibitUTF8Char (utf81 x) = false
checkProhibitUTF8Char (utf82 x) = case (TableC.CasesForUTF82.check (utf82 x)) of λ where
  true → true
  false → TableA1.CasesForUTF82.check (utf82 x)
checkProhibitUTF8Char (utf83 x) = case (TableC.CasesForUTF83.check (utf83 x)) of λ where
  true → true
  false → TableA1.CasesForUTF83.check (utf83 x)
checkProhibitUTF8Char (utf84 x) = case (TableC.CasesForUTF84.check (utf84 x)) of λ where
  true → true
  false → TableA1.CasesForUTF84.check (utf84 x)
