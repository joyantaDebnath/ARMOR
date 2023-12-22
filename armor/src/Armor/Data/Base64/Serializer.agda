{-# OPTIONS --inversion-max-depth=100 #-}

open import Armor.Binary
import      Armor.Data.Base64.TCB as Base64
import      Armor.Grammar.IList
import      Armor.Grammar.Serializer
open import Armor.Prelude

module Armor.Data.Base64.Serializer where

open Armor.Grammar.IList      Char
open Armor.Grammar.Serializer Char

open ≡-Reasoning

module Base64Char where
  serialize : Serializer Base64.Base64Char
  serialize (Base64.mk64 c c∈ i refl) =
    singleton [ lookup Base64.charset (↑ i) ]
      (cong (_∷ []) $ begin
        lookup Base64.charset (↑ i) ≡⟨ cong (lookup Base64.charset) (Singleton.x≡ i) ⟩
        lookup Base64.charset (Any.index c∈) ≡⟨ Lemmas.lookup-index c∈ ⟩
        c ∎)
    

module Base64Pad where
  open ≡-Reasoning

  serialize : Serializer Base64.Base64Pad
  serialize (Base64.pad0 refl) = self
  serialize (Base64.pad1 (Base64.mk64P1{b₁}{b₂}{b₃} c₁ c₂ c₃ pad bs≡)) =
    let b₁' = Base64Char.serialize c₁
        b₂' = Base64Char.serialize c₂
        b₃' = Base64Char.serialize c₃
    in
    singleton (↑ b₁' ++ ↑ b₂' ++ ↑ b₃' ++ [ '=' ])
      (begin (↑ b₁' ++ ↑ b₂' ++ ↑ b₃' ++ [ '=' ] ≡⟨ cong (_++ _) (Singleton.x≡ b₁') ⟩
             b₁ ∷ ↑ b₂' ++ ↑ b₃' ++ [ '=' ] ≡⟨ cong ((b₁ ∷_) ∘ (_++ _)) (Singleton.x≡ b₂') ⟩
             b₁ ∷ b₂ ∷ ↑ b₃' ++ [ '=' ] ≡⟨ cong (λ x → _ ∷ _ ∷ x ++ _) (Singleton.x≡ b₃') ⟩
             b₁ ∷ b₂ ∷ b₃ ∷ [ '=' ] ≡⟨ sym bs≡ ⟩
             _ ∎))
  serialize (Base64.pad2 (Base64.mk64P2{b₁}{b₂} c₁ c₂ pad bs≡)) =
    let b₁' = Base64Char.serialize c₁
        b₂' = Base64Char.serialize c₂
    in
    singleton (↑ b₁' ++ ↑ b₂' ++ '=' ∷ [ '=' ])
      (begin (↑ b₁' ++ ↑ b₂' ++ '=' ∷ [ '=' ] ≡⟨ cong (_++ _) (Singleton.x≡ b₁') ⟩
             b₁ ∷ ↑ b₂' ++ '=' ∷ [ '=' ] ≡⟨ cong ((b₁ ∷_) ∘ (_++ _)) (Singleton.x≡ b₂') ⟩
             b₁ ∷ b₂ ∷ '=' ∷ [ '=' ] ≡⟨ sym bs≡ ⟩
             _ ∎))

module Base64Str where
  serialize : Serializer Base64.Base64Str
  (serialize (Base64.mk64Str{bs₁}{bs₂} str strLen pad bs≡)) =
    let s = serializeIList Base64Char.serialize str
        p = Base64Pad.serialize pad
    in
    singleton (↑ s ++ ↑ p)
      (begin (↑ s ++ ↑ p ≡⟨ cong₂ _++_ (Singleton.x≡ s) (Singleton.x≡ p) ⟩
             bs₁ ++ bs₂ ≡⟨ sym bs≡ ⟩
             _ ∎))
    where open ≡-Reasoning

