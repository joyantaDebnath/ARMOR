open import Armor.Binary.Bits
import      Armor.Binary.Base64EncDec.Base64 as Base64
open import Armor.Binary.Base64EncDec.EncDec.Bytes.TCB
open import Armor.Prelude

module Armor.Binary.Base64EncDec.EncDec.Bytes.Properties where

@0 base256To64∘base64To256 : ∀ xs → base256To64 (base64To256 xs) ≡ xs
base256To64∘base64To256
  (  (b₁₁ ∷ b₁₂ ∷ b₁₃ ∷ b₁₄ ∷ b₁₅ ∷ b₁₆ ∷ [])
   ∷ (b₂₁ ∷ b₂₂ ∷ b₂₃ ∷ b₂₄ ∷ b₂₅ ∷ b₂₆ ∷ [])
   ∷ (b₃₁ ∷ b₃₂ ∷ b₃₃ ∷ b₃₄ ∷ b₃₅ ∷ b₃₆ ∷ [])
   ∷ (b₄₁ ∷ b₄₂ ∷ b₄₃ ∷ b₄₄ ∷ b₄₅ ∷ b₄₆ ∷ [])
   ∷ []) = refl

@0 base64To256∘base256To64 : ∀ xs → base64To256 (base256To64 xs) ≡ xs
base64To256∘base256To64
  (  (b₁₁ ∷ b₁₂ ∷ b₁₃ ∷ b₁₄ ∷ b₁₅ ∷ b₁₆ ∷ b₁₇ ∷ b₁₈ ∷ [])
   ∷ (b₂₁ ∷ b₂₂ ∷ b₂₃ ∷ b₂₄ ∷ b₂₅ ∷ b₂₆ ∷ b₂₇ ∷ b₂₈ ∷ [])
   ∷ (b₃₁ ∷ b₃₂ ∷ b₃₃ ∷ b₃₄ ∷ b₃₅ ∷ b₃₆ ∷ b₃₇ ∷ b₃₈ ∷ [])
   ∷ []) = refl
