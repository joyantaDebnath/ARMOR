{-# OPTIONS --sized-types #-}

open import Armor.Binary
open import Armor.Prelude
open import Armor.Data.Unicode.UTF8.TCB
open import Armor.Data.Unicode.UTF8.Trie
import      Armor.Grammar.IList

open import Armor.Data.X509.Semantic.StringPrep.ExcludeRange

module Armor.Data.X509.Semantic.StringPrep.InitMap.M2 where

open Armor.Grammar.IList UInt8

module DeleteList where

  module CasesForUTF81 where
    case1 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case1 c = ⌊ (inRangeAndFilter? 1 ((0 , 0 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c) ⌋

    case2 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case2 c = ⌊ (inRangeAndFilter? 1 ((1 , 1 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c) ⌋

    case3 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case3 c = ⌊ (inRangeAndFilter? 1 ((2 , 2 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c) ⌋

    case4 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case4 c = ⌊ (inRangeAndFilter? 1 ((3 , 3 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c) ⌋

    case5 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case5 c = ⌊ (inRangeAndFilter? 1 ((4 , 4 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c) ⌋

    case6 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case6 c = ⌊ (inRangeAndFilter? 1 ((5 , 5 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c) ⌋

    case7 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case7 c = ⌊ (inRangeAndFilter? 1 ((6 , 6 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c) ⌋

    case8 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case8 c = ⌊ (inRangeAndFilter? 1 ((7 , 7 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c) ⌋

    case9 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case9 c = ⌊ (inRangeAndFilter? 1 ((8 , 8 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c) ⌋

    case10 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case10 c = ⌊ (inRangeAndFilter? 1 ((14 , 14 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c) ⌋

    case11 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case11 c = ⌊ (inRangeAndFilter? 1 ((15 , 15 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c) ⌋

    case12 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case12 c = ⌊ (inRangeAndFilter? 1 ((16 , 16 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c) ⌋

    case13 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case13 c = ⌊ (inRangeAndFilter? 1 ((17 , 17 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c) ⌋

    case14 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case14 c = ⌊ (inRangeAndFilter? 1 ((18 , 18 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c) ⌋

    case15 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case15 c = ⌊ (inRangeAndFilter? 1 ((19 , 19 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c) ⌋

    case16 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case16 c = ⌊ (inRangeAndFilter? 1 ((20 , 20 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c) ⌋

    case17 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case17 c = ⌊ (inRangeAndFilter? 1 ((21 , 21 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c) ⌋

    case18 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case18 c = ⌊ (inRangeAndFilter? 1 ((22 , 22 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c) ⌋

    case19 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case19 c = ⌊ (inRangeAndFilter? 1 ((23 , 23 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c) ⌋

    case20 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case20 c = ⌊ (inRangeAndFilter? 1 ((24 , 24 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c) ⌋

    case21 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case21 c = ⌊ (inRangeAndFilter? 1 ((25 , 25 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c) ⌋

    case22 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case22 c = ⌊ (inRangeAndFilter? 1 ((26 , 26 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c) ⌋

    case23 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case23 c = ⌊ (inRangeAndFilter? 1 ((27 , 27 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c) ⌋

    case24 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case24 c = ⌊ (inRangeAndFilter? 1 ((28 , 28 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c) ⌋

    case25 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case25 c = ⌊ (inRangeAndFilter? 1 ((29 , 29 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c) ⌋

    case26 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case26 c = ⌊ (inRangeAndFilter? 1 ((30 , 30 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c) ⌋

    case27 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case27 c = ⌊ (inRangeAndFilter? 1 ((31 , 31 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c) ⌋

    case28 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case28 c = ⌊ (inRangeAndFilter? 1 ((127 , 127 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c) ⌋

    check : ∀ {@0 bs} → UTF8Char bs → Bool
    check x = or (List.map (λ f → f x) fs)
      where
      fs : List (∀ {@0 bs} → UTF8Char bs → Bool)
      fs = case1 ∷ case2 ∷ case3 ∷ case4 ∷ case5 ∷ case6 ∷ case7 ∷ case8 ∷ case9 ∷ case10 ∷ case11 ∷ case12 ∷ case13 ∷ case14 ∷ case15 ∷ case16 ∷ case17 ∷ case18 ∷ case19 ∷ case20 ∷ case21 ∷ case22 ∷ case23 ∷ case24 ∷ case25 ∷ case26 ∷ case27 ∷ case28 ∷ []

  module CasesForUTF82 where
    case1 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case1 c = ⌊ inRangeAndFilter? 2 ((194 , 194 , const ⊤ , (λ x → yes tt)) Vec.∷ (173 , 173 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c ⌋

    case2 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case2 c = ⌊ inRangeAndFilter? 2 ((194 , 194 , const ⊤ , (λ x → yes tt)) Vec.∷ (128 , 128 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c ⌋

    case3 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case3 c = ⌊ inRangeAndFilter? 2 ((194 , 194 , const ⊤ , (λ x → yes tt)) Vec.∷ (129 , 129 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c ⌋

    case4 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case4 c = ⌊ inRangeAndFilter? 2 ((194 , 194 , const ⊤ , (λ x → yes tt)) Vec.∷ (130 , 130 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c ⌋

    case5 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case5 c = ⌊ inRangeAndFilter? 2 ((194 , 194 , const ⊤ , (λ x → yes tt)) Vec.∷ (131 , 131 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c ⌋

    case6 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case6 c = ⌊ inRangeAndFilter? 2 ((194 , 194 , const ⊤ , (λ x → yes tt)) Vec.∷ (132 , 132 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c ⌋

    case7 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case7 c = ⌊ inRangeAndFilter? 2 ((194 , 194 , const ⊤ , (λ x → yes tt)) Vec.∷ (134 , 134 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c ⌋

    case8 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case8 c = ⌊ inRangeAndFilter? 2 ((194 , 194 , const ⊤ , (λ x → yes tt)) Vec.∷ (135 , 135 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c ⌋

    case9 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case9 c = ⌊ inRangeAndFilter? 2 ((194 , 194 , const ⊤ , (λ x → yes tt)) Vec.∷ (136 , 136 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c ⌋

    case10 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case10 c = ⌊ inRangeAndFilter? 2 ((194 , 194 , const ⊤ , (λ x → yes tt)) Vec.∷ (137 , 137 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c ⌋

    case11 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case11 c = ⌊ inRangeAndFilter? 2 ((194 , 194 , const ⊤ , (λ x → yes tt)) Vec.∷ (138 , 138 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c ⌋

    case12 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case12 c = ⌊ inRangeAndFilter? 2 ((194 , 194 , const ⊤ , (λ x → yes tt)) Vec.∷ (139 , 139 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c ⌋

    case13 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case13 c = ⌊ inRangeAndFilter? 2 ((194 , 194 , const ⊤ , (λ x → yes tt)) Vec.∷ (140 , 140 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c ⌋

    case14 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case14 c = ⌊ inRangeAndFilter? 2 ((194 , 194 , const ⊤ , (λ x → yes tt)) Vec.∷ (141 , 141 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c ⌋

    case15 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case15 c = ⌊ inRangeAndFilter? 2 ((194 , 194 , const ⊤ , (λ x → yes tt)) Vec.∷ (142 , 142 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c ⌋

    case16 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case16 c = ⌊ inRangeAndFilter? 2 ((194 , 194 , const ⊤ , (λ x → yes tt)) Vec.∷ (143 , 143 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c ⌋

    case17 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case17 c = ⌊ inRangeAndFilter? 2 ((194 , 194 , const ⊤ , (λ x → yes tt)) Vec.∷ (144 , 144 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c ⌋

    case18 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case18 c = ⌊ inRangeAndFilter? 2 ((194 , 194 , const ⊤ , (λ x → yes tt)) Vec.∷ (145 , 145 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c ⌋

    case19 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case19 c = ⌊ inRangeAndFilter? 2 ((194 , 194 , const ⊤ , (λ x → yes tt)) Vec.∷ (146 , 146 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c ⌋

    case20 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case20 c = ⌊ inRangeAndFilter? 2 ((194 , 194 , const ⊤ , (λ x → yes tt)) Vec.∷ (147 , 147 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c ⌋

    case21 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case21 c = ⌊ inRangeAndFilter? 2 ((194 , 194 , const ⊤ , (λ x → yes tt)) Vec.∷ (148 , 148 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c ⌋

    case22 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case22 c = ⌊ inRangeAndFilter? 2 ((194 , 194 , const ⊤ , (λ x → yes tt)) Vec.∷ (149 , 149 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c ⌋

    case23 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case23 c = ⌊ inRangeAndFilter? 2 ((194 , 194 , const ⊤ , (λ x → yes tt)) Vec.∷ (150 , 150 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c ⌋

    case24 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case24 c = ⌊ inRangeAndFilter? 2 ((194 , 194 , const ⊤ , (λ x → yes tt)) Vec.∷ (151 , 151 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c ⌋

    case25 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case25 c = ⌊ inRangeAndFilter? 2 ((194 , 194 , const ⊤ , (λ x → yes tt)) Vec.∷ (152 , 152 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c ⌋

    case26 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case26 c = ⌊ inRangeAndFilter? 2 ((194 , 194 , const ⊤ , (λ x → yes tt)) Vec.∷ (153 , 153 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c ⌋

    case27 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case27 c = ⌊ inRangeAndFilter? 2 ((194 , 194 , const ⊤ , (λ x → yes tt)) Vec.∷ (154 , 154 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c ⌋

    case28 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case28 c = ⌊ inRangeAndFilter? 2 ((194 , 194 , const ⊤ , (λ x → yes tt)) Vec.∷ (155 , 155 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c ⌋

    case29 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case29 c = ⌊ inRangeAndFilter? 2 ((194 , 194 , const ⊤ , (λ x → yes tt)) Vec.∷ (156 , 156 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c ⌋

    case30 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case30 c = ⌊ inRangeAndFilter? 2 ((194 , 194 , const ⊤ , (λ x → yes tt)) Vec.∷ (157 , 157 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c ⌋

    case31 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case31 c = ⌊ inRangeAndFilter? 2 ((194 , 194 , const ⊤ , (λ x → yes tt)) Vec.∷ (158 , 158 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c ⌋

    case32 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case32 c = ⌊ inRangeAndFilter? 2 ((194 , 194 , const ⊤ , (λ x → yes tt)) Vec.∷ (159 , 159 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c ⌋

    case33 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case33 c = ⌊ inRangeAndFilter? 2 ((205 , 205 , const ⊤ , (λ x → yes tt)) Vec.∷ (143 , 143 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c ⌋

    case34 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case34 c = ⌊ inRangeAndFilter? 2 ((219 , 219 , const ⊤ , (λ x → yes tt)) Vec.∷ (157 , 157 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c ⌋

    case35 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case35 c = ⌊ inRangeAndFilter? 2 ((220 , 220 , const ⊤ , (λ x → yes tt)) Vec.∷ (143 , 143 , const ⊤ , (λ x → yes tt)) Vec.∷ Vec.[]) c ⌋

    check : ∀ {@0 bs} → UTF8Char bs → Bool
    check x = or (List.map (λ f → f x) fs)
      where
      fs : List (∀ {@0 bs} → UTF8Char bs → Bool)
      fs = case1 ∷ case2 ∷ case3 ∷ case4 ∷ case5 ∷ case6 ∷ case7 ∷ case8 ∷ case9 ∷ case10 ∷ case11 ∷ case12 ∷ case13 ∷ case14 ∷ case15 ∷ case16 ∷ case17 ∷ case18 ∷ case19 ∷ case20 ∷ case21 ∷ case22 ∷ case23 ∷ case24 ∷ case25 ∷ case26 ∷ case27 ∷ case28 ∷ case29 ∷ case30 ∷ case31 ∷ case32 ∷ case33 ∷ case34 ∷ case35 ∷ []

  module CasesForUTF83 where
    case1 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case1 c = ⌊ inRangeAndFilter? 3 (((225 , 225 , const ⊤ , (λ x → yes tt))) Vec.∷ ((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((139 , 139 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case2 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case2 c = ⌊ inRangeAndFilter? 3 (((225 , 225 , const ⊤ , (λ x → yes tt))) Vec.∷ ((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((140 , 140 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case3 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case3 c = ⌊ inRangeAndFilter? 3 (((225 , 225 , const ⊤ , (λ x → yes tt))) Vec.∷ ((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((141 , 141 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case4 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case4 c = ⌊ inRangeAndFilter? 3 (((225 , 225 , const ⊤ , (λ x → yes tt))) Vec.∷ ((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((142 , 142 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case5 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case5 c = ⌊ inRangeAndFilter? 3 (((225 , 225 , const ⊤ , (λ x → yes tt))) Vec.∷ ((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((134 , 134 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case6 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case6 c = ⌊ inRangeAndFilter? 3 (((226 , 226 , const ⊤ , (λ x → yes tt))) Vec.∷ ((128 , 128 , const ⊤ , (λ x → yes tt))) Vec.∷ (((139 , 139 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case7 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case7 c = ⌊ inRangeAndFilter? 3 (((226 , 226 , const ⊤ , (λ x → yes tt))) Vec.∷ ((128 , 128 , const ⊤ , (λ x → yes tt))) Vec.∷ (((140 , 140 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case8 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case8 c = ⌊ inRangeAndFilter? 3 (((226 , 226 , const ⊤ , (λ x → yes tt))) Vec.∷ ((128 , 128 , const ⊤ , (λ x → yes tt))) Vec.∷ (((141 , 141 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case9 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case9 c = ⌊ inRangeAndFilter? 3 (((226 , 226 , const ⊤ , (λ x → yes tt))) Vec.∷ ((128 , 128 , const ⊤ , (λ x → yes tt))) Vec.∷ (((142 , 142 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case10 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case10 c = ⌊ inRangeAndFilter? 3 (((226 , 226 , const ⊤ , (λ x → yes tt))) Vec.∷ ((128 , 128 , const ⊤ , (λ x → yes tt))) Vec.∷ (((143 , 143 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case11 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case11 c = ⌊ inRangeAndFilter? 3 (((226 , 226 , const ⊤ , (λ x → yes tt))) Vec.∷ ((128 , 128 , const ⊤ , (λ x → yes tt))) Vec.∷ (((170 , 170 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case12 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case12 c = ⌊ inRangeAndFilter? 3 (((226 , 226 , const ⊤ , (λ x → yes tt))) Vec.∷ ((128 , 128 , const ⊤ , (λ x → yes tt))) Vec.∷ (((171 , 171 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case13 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case13 c = ⌊ inRangeAndFilter? 3 (((226 , 226 , const ⊤ , (λ x → yes tt))) Vec.∷ ((128 , 128 , const ⊤ , (λ x → yes tt))) Vec.∷ (((172 , 172 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case14 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case14 c = ⌊ inRangeAndFilter? 3 (((226 , 226 , const ⊤ , (λ x → yes tt))) Vec.∷ ((128 , 128 , const ⊤ , (λ x → yes tt))) Vec.∷ (((173 , 173 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case15 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case15 c = ⌊ inRangeAndFilter? 3 (((226 , 226 , const ⊤ , (λ x → yes tt))) Vec.∷ ((128 , 128 , const ⊤ , (λ x → yes tt))) Vec.∷ (((174 , 174 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case16 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case16 c = ⌊ inRangeAndFilter? 3 (((226 , 226 , const ⊤ , (λ x → yes tt))) Vec.∷ ((129 , 129 , const ⊤ , (λ x → yes tt))) Vec.∷ (((170 , 170 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case17 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case17 c = ⌊ inRangeAndFilter? 3 (((226 , 226 , const ⊤ , (λ x → yes tt))) Vec.∷ ((129 , 129 , const ⊤ , (λ x → yes tt))) Vec.∷ (((171 , 171 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case18 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case18 c = ⌊ inRangeAndFilter? 3 (((226 , 226 , const ⊤ , (λ x → yes tt))) Vec.∷ ((129 , 129 , const ⊤ , (λ x → yes tt))) Vec.∷ (((172 , 172 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case19 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case19 c = ⌊ inRangeAndFilter? 3 (((226 , 226 , const ⊤ , (λ x → yes tt))) Vec.∷ ((129 , 129 , const ⊤ , (λ x → yes tt))) Vec.∷ (((173 , 173 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case20 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case20 c = ⌊ inRangeAndFilter? 3 (((226 , 226 , const ⊤ , (λ x → yes tt))) Vec.∷ ((129 , 129 , const ⊤ , (λ x → yes tt))) Vec.∷ (((174 , 174 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case21 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case21 c = ⌊ inRangeAndFilter? 3 (((226 , 226 , const ⊤ , (λ x → yes tt))) Vec.∷ ((129 , 129 , const ⊤ , (λ x → yes tt))) Vec.∷ (((175 , 175 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case22 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case22 c = ⌊ inRangeAndFilter? 3 (((226 , 226 , const ⊤ , (λ x → yes tt))) Vec.∷ ((129 , 129 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case23 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case23 c = ⌊ inRangeAndFilter? 3 (((226 , 226 , const ⊤ , (λ x → yes tt))) Vec.∷ ((129 , 129 , const ⊤ , (λ x → yes tt))) Vec.∷ (((161 , 161 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case24 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case24 c = ⌊ inRangeAndFilter? 3 (((226 , 226 , const ⊤ , (λ x → yes tt))) Vec.∷ ((129 , 129 , const ⊤ , (λ x → yes tt))) Vec.∷ (((162 , 162 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case25 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case25 c = ⌊ inRangeAndFilter? 3 (((226 , 226 , const ⊤ , (λ x → yes tt))) Vec.∷ ((129 , 129 , const ⊤ , (λ x → yes tt))) Vec.∷ (((163 , 163 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case26 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case26 c = ⌊ inRangeAndFilter? 3 (((239 , 239 , const ⊤ , (λ x → yes tt))) Vec.∷ ((187 , 187 , const ⊤ , (λ x → yes tt))) Vec.∷ (((191 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case27 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case27 c = ⌊ inRangeAndFilter? 3 (((239 , 239 , const ⊤ , (λ x → yes tt))) Vec.∷ ((191 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ (((185 , 185 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case28 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case28 c = ⌊ inRangeAndFilter? 3 (((239 , 239 , const ⊤ , (λ x → yes tt))) Vec.∷ ((191 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ (((186 , 186 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case29 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case29 c = ⌊ inRangeAndFilter? 3 (((239 , 239 , const ⊤ , (λ x → yes tt))) Vec.∷ ((191 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ (((187 , 187 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    case30 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case30 c = ⌊ inRangeAndFilter? 3 (((239 , 239 , const ⊤ , (λ x → yes tt))) Vec.∷ ((191 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ (((188 , 188 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])) c ⌋

    check : ∀ {@0 bs} → UTF8Char bs → Bool
    check x = or (List.map (λ f → f x) fs)
      where
      fs : List (∀ {@0 bs} → UTF8Char bs → Bool)
      fs = case1 ∷ case2 ∷ case3 ∷ case4 ∷ case5 ∷ case6 ∷ case7 ∷ case8 ∷ case9 ∷ case10 ∷ case11 ∷ case12 ∷ case13 ∷ case14 ∷ case15 ∷ case16 ∷ case17 ∷ case18 ∷ case19 ∷ case20 ∷ case21 ∷ case22 ∷ case23 ∷ case24 ∷ case25 ∷ case26 ∷ case27 ∷ case28 ∷ case29 ∷ case30 ∷ []

  module CasesForUTF84 where
    case1 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case1 c = ⌊ inRangeAndFilter? 4 (((240 , 240 , const ⊤ , (λ x → yes tt))) Vec.∷ (((157 , 157 , const ⊤ , (λ x → yes tt))) Vec.∷ (((133 , 133 , const ⊤ , (λ x → yes tt))) Vec.∷ (((179 , 179 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case2 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case2 c = ⌊ inRangeAndFilter? 4 (((240 , 240 , const ⊤ , (λ x → yes tt))) Vec.∷ (((157 , 157 , const ⊤ , (λ x → yes tt))) Vec.∷ (((133 , 133 , const ⊤ , (λ x → yes tt))) Vec.∷ (((180 , 180 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case3 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case3 c = ⌊ inRangeAndFilter? 4 (((240 , 240 , const ⊤ , (λ x → yes tt))) Vec.∷ (((157 , 157 , const ⊤ , (λ x → yes tt))) Vec.∷ (((133 , 133 , const ⊤ , (λ x → yes tt))) Vec.∷ (((181 , 181 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case4 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case4 c = ⌊ inRangeAndFilter? 4 (((240 , 240 , const ⊤ , (λ x → yes tt))) Vec.∷ (((157 , 157 , const ⊤ , (λ x → yes tt))) Vec.∷ (((133 , 133 , const ⊤ , (λ x → yes tt))) Vec.∷ (((182 , 182 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case5 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case5 c = ⌊ inRangeAndFilter? 4 (((240 , 240 , const ⊤ , (λ x → yes tt))) Vec.∷ (((157 , 157 , const ⊤ , (λ x → yes tt))) Vec.∷ (((133 , 133 , const ⊤ , (λ x → yes tt))) Vec.∷ (((183 , 183 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case6 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case6 c = ⌊ inRangeAndFilter? 4 (((240 , 240 , const ⊤ , (λ x → yes tt))) Vec.∷ (((157 , 157 , const ⊤ , (λ x → yes tt))) Vec.∷ (((133 , 133 , const ⊤ , (λ x → yes tt))) Vec.∷ (((184 , 184 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case7 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case7 c = ⌊ inRangeAndFilter? 4 (((240 , 240 , const ⊤ , (λ x → yes tt))) Vec.∷ (((157 , 157 , const ⊤ , (λ x → yes tt))) Vec.∷ (((133 , 133 , const ⊤ , (λ x → yes tt))) Vec.∷ (((185 , 185 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case8 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case8 c = ⌊ inRangeAndFilter? 4 (((240 , 240 , const ⊤ , (λ x → yes tt))) Vec.∷ (((157 , 157 , const ⊤ , (λ x → yes tt))) Vec.∷ (((133 , 133 , const ⊤ , (λ x → yes tt))) Vec.∷ (((186 , 186 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case9 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case9 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 128 , const ⊤ , (λ x → yes tt))) Vec.∷ (((129 , 129 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case10 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case10 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 128 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case11 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case11 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 128 , const ⊤ , (λ x → yes tt))) Vec.∷ (((161 , 161 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case12 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case12 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 128 , const ⊤ , (λ x → yes tt))) Vec.∷ (((162 , 162 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case13 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case13 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 128 , const ⊤ , (λ x → yes tt))) Vec.∷ (((163 , 163 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case14 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case14 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 128 , const ⊤ , (λ x → yes tt))) Vec.∷ (((164 , 164 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case15 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case15 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 128 , const ⊤ , (λ x → yes tt))) Vec.∷ (((165 , 165 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case16 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case16 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 128 , const ⊤ , (λ x → yes tt))) Vec.∷ (((166 , 166 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case17 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case17 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 128 , const ⊤ , (λ x → yes tt))) Vec.∷ (((167 , 167 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case18 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case18 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 128 , const ⊤ , (λ x → yes tt))) Vec.∷ (((168 , 168 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case19 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case19 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 128 , const ⊤ , (λ x → yes tt))) Vec.∷ (((169 , 169 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case20 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case20 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 128 , const ⊤ , (λ x → yes tt))) Vec.∷ (((170 , 170 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case21 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case21 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 128 , const ⊤ , (λ x → yes tt))) Vec.∷ (((171 , 171 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case22 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case22 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 128 , const ⊤ , (λ x → yes tt))) Vec.∷ (((172 , 172 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case23 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case23 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 128 , const ⊤ , (λ x → yes tt))) Vec.∷ (((173 , 173 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case24 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case24 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 128 , const ⊤ , (λ x → yes tt))) Vec.∷ (((174 , 174 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case25 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case25 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 128 , const ⊤ , (λ x → yes tt))) Vec.∷ (((175 , 175 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case26 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case26 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 128 , const ⊤ , (λ x → yes tt))) Vec.∷ (((176 , 176 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case27 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case27 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 128 , const ⊤ , (λ x → yes tt))) Vec.∷ (((177 , 177 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case28 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case28 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 128 , const ⊤ , (λ x → yes tt))) Vec.∷ (((178 , 178 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case29 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case29 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 128 , const ⊤ , (λ x → yes tt))) Vec.∷ (((179 , 179 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case30 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case30 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 128 , const ⊤ , (λ x → yes tt))) Vec.∷ (((180 , 180 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case31 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case31 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 128 , const ⊤ , (λ x → yes tt))) Vec.∷ (((181 , 181 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case32 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case32 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 128 , const ⊤ , (λ x → yes tt))) Vec.∷ (((182 , 182 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case33 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case33 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 128 , const ⊤ , (λ x → yes tt))) Vec.∷ (((183 , 183 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case34 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case34 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 128 , const ⊤ , (λ x → yes tt))) Vec.∷ (((184 , 184 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case35 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case35 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 128 , const ⊤ , (λ x → yes tt))) Vec.∷ (((185 , 185 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case36 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case36 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 128 , const ⊤ , (λ x → yes tt))) Vec.∷ (((186 , 186 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case37 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case37 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 128 , const ⊤ , (λ x → yes tt))) Vec.∷ (((187 , 187 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case38 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case38 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 128 , const ⊤ , (λ x → yes tt))) Vec.∷ (((188 , 188 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case39 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case39 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 128 , const ⊤ , (λ x → yes tt))) Vec.∷ (((189 , 189 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case40 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case40 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 128 , const ⊤ , (λ x → yes tt))) Vec.∷ (((190 , 190 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case41 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case41 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 128 , const ⊤ , (λ x → yes tt))) Vec.∷ (((191 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case42 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case42 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((129 , 129 , const ⊤ , (λ x → yes tt))) Vec.∷ (((128 , 128 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case43 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case43 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((129 , 129 , const ⊤ , (λ x → yes tt))) Vec.∷ (((129 , 129 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case44 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case44 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((129 , 129 , const ⊤ , (λ x → yes tt))) Vec.∷ (((130 , 130 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case45 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case45 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((129 , 129 , const ⊤ , (λ x → yes tt))) Vec.∷ (((131 , 131 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case46 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case46 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((129 , 129 , const ⊤ , (λ x → yes tt))) Vec.∷ (((132 , 132 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case47 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case47 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((129 , 129 , const ⊤ , (λ x → yes tt))) Vec.∷ (((133 , 133 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case48 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case48 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((129 , 129 , const ⊤ , (λ x → yes tt))) Vec.∷ (((134 , 134 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case49 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case49 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((129 , 129 , const ⊤ , (λ x → yes tt))) Vec.∷ (((135 , 135 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case50 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case50 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((129 , 129 , const ⊤ , (λ x → yes tt))) Vec.∷ (((136 , 136 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case51 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case51 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((129 , 129 , const ⊤ , (λ x → yes tt))) Vec.∷ (((137 , 137 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case52 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case52 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((129 , 129 , const ⊤ , (λ x → yes tt))) Vec.∷ (((138 , 138 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case53 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case53 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((129 , 129 , const ⊤ , (λ x → yes tt))) Vec.∷ (((139 , 139 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case54 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case54 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((129 , 129 , const ⊤ , (λ x → yes tt))) Vec.∷ (((140 , 140 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case55 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case55 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((129 , 129 , const ⊤ , (λ x → yes tt))) Vec.∷ (((141 , 141 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case56 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case56 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((129 , 129 , const ⊤ , (λ x → yes tt))) Vec.∷ (((142 , 142 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case57 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case57 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((129 , 129 , const ⊤ , (λ x → yes tt))) Vec.∷ (((143 , 143 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case58 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case58 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((129 , 129 , const ⊤ , (λ x → yes tt))) Vec.∷ (((144 , 144 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case59 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case59 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((129 , 129 , const ⊤ , (λ x → yes tt))) Vec.∷ (((145 , 145 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case60 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case60 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((129 , 129 , const ⊤ , (λ x → yes tt))) Vec.∷ (((146 , 146 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case61 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case61 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((129 , 129 , const ⊤ , (λ x → yes tt))) Vec.∷ (((147 , 147 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case62 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case62 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((129 , 129 , const ⊤ , (λ x → yes tt))) Vec.∷ (((148 , 148 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case63 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case63 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((129 , 129 , const ⊤ , (λ x → yes tt))) Vec.∷ (((149 , 149 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case64 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case64 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((129 , 129 , const ⊤ , (λ x → yes tt))) Vec.∷ (((150 , 150 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case65 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case65 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((129 , 129 , const ⊤ , (λ x → yes tt))) Vec.∷ (((151 , 151 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case66 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case66 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((129 , 129 , const ⊤ , (λ x → yes tt))) Vec.∷ (((152 , 152 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case67 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case67 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((129 , 129 , const ⊤ , (λ x → yes tt))) Vec.∷ (((153 , 153 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case68 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case68 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((129 , 129 , const ⊤ , (λ x → yes tt))) Vec.∷ (((154 , 154 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case69 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case69 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((129 , 129 , const ⊤ , (λ x → yes tt))) Vec.∷ (((155 , 155 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case70 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case70 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((129 , 129 , const ⊤ , (λ x → yes tt))) Vec.∷ (((156 , 156 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case71 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case71 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((129 , 129 , const ⊤ , (λ x → yes tt))) Vec.∷ (((157 , 157 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case72 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case72 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((129 , 129 , const ⊤ , (λ x → yes tt))) Vec.∷ (((158 , 158 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case73 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case73 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((129 , 129 , const ⊤ , (λ x → yes tt))) Vec.∷ (((159 , 159 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case74 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case74 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((129 , 129 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case75 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case75 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((129 , 129 , const ⊤ , (λ x → yes tt))) Vec.∷ (((161 , 161 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case76 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case76 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((129 , 129 , const ⊤ , (λ x → yes tt))) Vec.∷ (((162 , 162 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case77 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case77 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((129 , 129 , const ⊤ , (λ x → yes tt))) Vec.∷ (((163 , 163 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case78 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case78 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((129 , 129 , const ⊤ , (λ x → yes tt))) Vec.∷ (((164 , 164 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case79 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case79 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((129 , 129 , const ⊤ , (λ x → yes tt))) Vec.∷ (((165 , 165 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case80 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case80 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((129 , 129 , const ⊤ , (λ x → yes tt))) Vec.∷ (((166 , 166 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case81 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case81 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((129 , 129 , const ⊤ , (λ x → yes tt))) Vec.∷ (((167 , 167 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case82 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case82 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((129 , 129 , const ⊤ , (λ x → yes tt))) Vec.∷ (((168 , 168 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case83 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case83 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((129 , 129 , const ⊤ , (λ x → yes tt))) Vec.∷ (((169 , 169 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case84 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case84 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((129 , 129 , const ⊤ , (λ x → yes tt))) Vec.∷ (((170 , 170 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case85 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case85 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((129 , 129 , const ⊤ , (λ x → yes tt))) Vec.∷ (((171 , 171 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case86 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case86 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((129 , 129 , const ⊤ , (λ x → yes tt))) Vec.∷ (((172 , 172 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case87 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case87 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((129 , 129 , const ⊤ , (λ x → yes tt))) Vec.∷ (((173 , 173 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case88 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case88 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((129 , 129 , const ⊤ , (λ x → yes tt))) Vec.∷ (((174 , 174 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case89 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case89 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((129 , 129 , const ⊤ , (λ x → yes tt))) Vec.∷ (((175 , 175 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case90 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case90 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((129 , 129 , const ⊤ , (λ x → yes tt))) Vec.∷ (((176 , 176 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case91 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case91 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((129 , 129 , const ⊤ , (λ x → yes tt))) Vec.∷ (((177 , 177 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case92 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case92 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((129 , 129 , const ⊤ , (λ x → yes tt))) Vec.∷ (((178 , 178 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case93 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case93 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((129 , 129 , const ⊤ , (λ x → yes tt))) Vec.∷ (((179 , 179 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case94 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case94 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((129 , 129 , const ⊤ , (λ x → yes tt))) Vec.∷ (((180 , 180 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case95 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case95 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((129 , 129 , const ⊤ , (λ x → yes tt))) Vec.∷ (((181 , 181 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case96 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case96 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((129 , 129 , const ⊤ , (λ x → yes tt))) Vec.∷ (((182 , 182 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case97 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case97 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((129 , 129 , const ⊤ , (λ x → yes tt))) Vec.∷ (((183 , 183 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case98 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case98 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((129 , 129 , const ⊤ , (λ x → yes tt))) Vec.∷ (((184 , 184 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case99 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case99 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((129 , 129 , const ⊤ , (λ x → yes tt))) Vec.∷ (((185 , 185 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case100 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case100 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((129 , 129 , const ⊤ , (λ x → yes tt))) Vec.∷ (((186 , 186 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case101 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case101 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((129 , 129 , const ⊤ , (λ x → yes tt))) Vec.∷ (((187 , 187 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case102 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case102 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((129 , 129 , const ⊤ , (λ x → yes tt))) Vec.∷ (((188 , 188 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case103 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case103 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((129 , 129 , const ⊤ , (λ x → yes tt))) Vec.∷ (((189 , 189 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case104 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case104 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((129 , 129 , const ⊤ , (λ x → yes tt))) Vec.∷ (((190 , 190 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    case105 :  ∀ {@0 bs} → UTF8Char bs → Bool
    case105 c = ⌊ inRangeAndFilter? 4 (((243 , 243 , const ⊤ , (λ x → yes tt))) Vec.∷ (((160 , 160 , const ⊤ , (λ x → yes tt))) Vec.∷ (((129 , 129 , const ⊤ , (λ x → yes tt))) Vec.∷ (((191 , 191 , const ⊤ , (λ x → yes tt))) Vec.∷ Vec.[])))) c ⌋

    check : ∀ {@0 bs} → UTF8Char bs → Bool
    check x = or (List.map (λ f → f x) fs)
      where
      fs : List (∀ {@0 bs} → UTF8Char bs → Bool)
      fs = case1 ∷ case2 ∷ case3 ∷ case4 ∷ case5 ∷ case6 ∷ case7 ∷ case8 ∷ case9 ∷ case10 ∷ case11 ∷ case12 ∷ case13 ∷ case14 ∷ case15 ∷ case16 ∷ case17 ∷ case18 ∷ case19 ∷ case20 ∷ case21 ∷ case22 ∷ case23 ∷ case24 ∷ case25 ∷ case26 ∷ case27 ∷ case28 ∷ case29 ∷ case30 ∷ case31 ∷ case32 ∷ case33 ∷ case34 ∷ case35 ∷ case36 ∷ case37 ∷ case38 ∷ case39 ∷ case40 ∷ case41 ∷ case42 ∷ case43 ∷ case44 ∷ case45 ∷ case46 ∷ case47 ∷ case48 ∷ case49 ∷ case50 ∷ case51 ∷ case52 ∷ case53 ∷ case54 ∷ case55 ∷ case56 ∷ case57 ∷ case58 ∷ case59 ∷ case60 ∷ case61 ∷ case62 ∷ case63 ∷ case64 ∷ case65 ∷ case66 ∷ case67 ∷ case68 ∷ case69 ∷ case70 ∷ case71 ∷ case72 ∷ case73 ∷ case74 ∷ case75 ∷ case76 ∷ case77 ∷ case78 ∷ case79 ∷ case80 ∷ case81 ∷ case82 ∷ case83 ∷ case84 ∷ case85 ∷ case86 ∷ case87 ∷ case88 ∷ case89 ∷ case90 ∷ case91 ∷ case92 ∷ case93 ∷ case94 ∷ case95 ∷ case96 ∷ case97 ∷ case98 ∷ case99 ∷ case100 ∷ case101 ∷ case102 ∷ case103 ∷ case104 ∷ case105 ∷ []
