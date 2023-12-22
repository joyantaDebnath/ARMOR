open import Armor.Binary
open import Armor.Data.Unicode.UTF16.TCB
import      Armor.Grammar.Definitions
import      Armor.Grammar.IList
open import Armor.Prelude

module Armor.Data.Unicode.UTF16.Properties where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.IList       UInt8

module BMP where
  @0 nonempty : NonEmpty BMPChar
  nonempty (mkBMPChar c₁ c₂ range refl) ()

  @0 nosubstrings : NoSubstrings BMPChar
  nosubstrings refl (mkBMPChar c₁ c₂ range refl) (mkBMPChar .c₁ .c₂ range₁ refl) = refl

  private
    open import Data.Nat.Properties
      hiding (_≟_)
    open import Data.Sum.Properties
    open ≤-Reasoning

    @0 range≡ : {c : UInt8} → (r₁ r₂ : InRange 0 215 c ⊎ InRange 224 255 c) → r₁ ≡ r₂
    range≡ (inj₁ x) (inj₁ x₁) = cong inj₁ (inRange-unique{A = ℕ}{B = UInt8} x x₁)
    range≡{c} (inj₁ (_ , c₁≤215)) (inj₂ (c₁≥224 , _)) =
      contradiction{P = 224 ≤ 215}
        (begin
          224 ≤⟨ c₁≥224 ⟩
          toℕ c ≤⟨ c₁≤215 ⟩
          215 ∎)
        (toWitnessFalse{Q = 224 ≤? 215} tt)
    range≡{c} (inj₂ (c₁≥224 , _)) (inj₁ (_ , c₁≤215)) =
      contradiction{P = 224 ≤ 215}
        (begin
          224 ≤⟨ c₁≥224 ⟩
          toℕ c ≤⟨ c₁≤215 ⟩
          215 ∎)
        (toWitnessFalse{Q = 224 ≤? 215} tt)
    range≡ (inj₂ y) (inj₂ y₁) = cong inj₂ (inRange-unique{A = ℕ}{B = UInt8} y y₁)
  
  @0 unambiguous : Unambiguous BMPChar
  unambiguous (mkBMPChar c₁ c₂ range refl) (mkBMPChar .c₁ .c₂ range₁ refl) =
    subst (λ x → mkBMPChar c₁ c₂ range refl ≡ mkBMPChar c₁ c₂ x refl) (‼ range≡ range range₁) refl

  @0 nonmalleable : NonMalleable RawBMPChar
  nonmalleable (mkBMPChar c₁ c₂ range refl) (mkBMPChar c₃ c₄ range₁ refl) refl =
    case (‼ range≡ range range₁) of λ where
      refl → refl

  instance
    BMPEq≋ : Eq≋ BMPChar
    Eq≋._≋?_ BMPEq≋ (mkBMPChar c₁ c₂ range refl) (mkBMPChar c₃ c₄ range₁ refl)
      with c₁ ≟ c₃ | c₂ ≟ c₄
    ... | no ¬p | _ = no λ where (mk≋ refl a≡) → contradiction refl ¬p
    ... | yes refl | no ¬p = no λ where (mk≋ refl _) → contradiction refl ¬p
    ... | yes refl | yes refl =
      yes (mk≋ refl (subst (λ x → mkBMPChar c₁ c₂ range refl ≡ mkBMPChar c₁ c₂ x refl) (‼ range≡ range range₁) refl))
  
    eqBMP : Eq (Exists─ (List UInt8) BMPChar)
    eqBMP = Eq≋⇒Eq it

    UTF16Eq≋ : Eq≋ BMP
    UTF16Eq≋ = IList.IListEq≋

sizeUnique : ∀ {@0 bs} → (a₁ a₂ : BMP bs) → size a₁ ≡ size a₂
sizeUnique nil nil = refl
sizeUnique nil (consIList {_} {_} (mkBMPChar _ _ _ refl) t₂ ())
sizeUnique (consIList (mkBMPChar c₁₁ c₁₂ _ refl) t₁ ()) nil
sizeUnique (consIList (mkBMPChar c₁₁ c₁₂ _ refl) t₁ refl) (consIList (mkBMPChar ._ ._ _ refl) t₂ refl) =
  cong suc (sizeUnique t₁ t₂)

@0 unambiguous : Unambiguous BMP
unambiguous =
  IList.unambiguous
    BMP.unambiguous BMP.nonempty BMP.nosubstrings

@0 nonmalleable : NonMalleable RawBMP
nonmalleable = IList.nonmalleable BMP.nonempty BMP.nosubstrings BMP.nonmalleable
