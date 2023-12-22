open import Armor.Binary.Bits
import      Armor.Binary.Base64EncDec.Base64 as Base64
open import Armor.Prelude

module Armor.Binary.Base64EncDec.EncDec.Bytes.TCB where

base64To256 : Vec (Binary 6) 4 → Vec (Binary 8) 3
base64To256
  (  (b₁₁ ∷ b₁₂ ∷ b₁₃ ∷ b₁₄ ∷ b₁₅ ∷ b₁₆ ∷ [])
   ∷ (b₂₁ ∷ b₂₂ ∷ b₂₃ ∷ b₂₄ ∷ b₂₅ ∷ b₂₆ ∷ [])
   ∷ (b₃₁ ∷ b₃₂ ∷ b₃₃ ∷ b₃₄ ∷ b₃₅ ∷ b₃₆ ∷ [])
   ∷ (b₄₁ ∷ b₄₂ ∷ b₄₃ ∷ b₄₄ ∷ b₄₅ ∷ b₄₆ ∷ [])
   ∷ [])
  =   (b₁₁ ∷ b₁₂ ∷ b₁₃ ∷ b₁₄ ∷ b₁₅ ∷ b₁₆ ∷ b₂₁ ∷ b₂₂ ∷ [])
    ∷ (b₂₃ ∷ b₂₄ ∷ b₂₅ ∷ b₂₆ ∷ b₃₁ ∷ b₃₂ ∷ b₃₃ ∷ b₃₄ ∷ [])
    ∷ (b₃₅ ∷ b₃₆ ∷ b₄₁ ∷ b₄₂ ∷ b₄₃ ∷ b₄₄ ∷ b₄₅ ∷ b₄₆ ∷ [])
    ∷ []

base256To64 : Vec (Binary 8) 3 → Vec (Binary 6) 4
base256To64
  (  (b₁₁ ∷ b₁₂ ∷ b₁₃ ∷ b₁₄ ∷ b₁₅ ∷ b₁₆ ∷ b₁₇ ∷ b₁₈ ∷ [])
   ∷ (b₂₁ ∷ b₂₂ ∷ b₂₃ ∷ b₂₄ ∷ b₂₅ ∷ b₂₆ ∷ b₂₇ ∷ b₂₈ ∷ [])
   ∷ (b₃₁ ∷ b₃₂ ∷ b₃₃ ∷ b₃₄ ∷ b₃₅ ∷ b₃₆ ∷ b₃₇ ∷ b₃₈ ∷ [])
   ∷ []) =
     (b₁₁ ∷ b₁₂ ∷ b₁₃ ∷ b₁₄ ∷ b₁₅ ∷ Vec.[ b₁₆ ])
   ∷ (b₁₇ ∷ b₁₈ ∷ b₂₁ ∷ b₂₂ ∷ b₂₃ ∷ Vec.[ b₂₄ ])
   ∷ (b₂₅ ∷ b₂₆ ∷ b₂₇ ∷ b₂₈ ∷ b₃₁ ∷ Vec.[ b₃₂ ])
   ∷ Vec.[ b₃₃ ∷ b₃₄ ∷ b₃₅ ∷ b₃₆ ∷ b₃₇ ∷ Vec.[ b₃₈ ] ]

pad64To256 : Base64.Pad → List (Binary 8)
pad64To256 (Base64.pad2 (
    (b₁₁ ∷ b₁₂ ∷ b₁₃ ∷ b₁₄ ∷ b₁₅ ∷ b₁₆ ∷ [])
  ∷ (b₂₁ ∷ b₂₂ ∷ b₂₃ ∷ b₂₄ ∷ b₂₅ ∷ b₂₆ ∷ [])
  ∷ []))
  = [ b₁₁ ∷ b₁₂ ∷ b₁₃ ∷ b₁₄ ∷ b₁₅ ∷ b₁₆ ∷ b₂₁ ∷ b₂₂ ∷ [] ]
pad64To256 (Base64.pad1 (
    (b₁₁ ∷ b₁₂ ∷ b₁₃ ∷ b₁₄ ∷ b₁₅ ∷ b₁₆ ∷ [])
  ∷ (b₂₁ ∷ b₂₂ ∷ b₂₃ ∷ b₂₄ ∷ b₂₅ ∷ b₂₆ ∷ [])
  ∷ (b₃₁ ∷ b₃₂ ∷ b₃₃ ∷ b₃₄ ∷ b₃₅ ∷ b₃₆ ∷ [])
  ∷ []))
  =   (b₁₁ ∷ b₁₂ ∷ b₁₃ ∷ b₁₄ ∷ b₁₅ ∷ b₁₆ ∷ b₂₁ ∷ b₂₂ ∷ [])
    ∷ (b₂₃ ∷ b₂₄ ∷ b₂₅ ∷ b₂₆ ∷ b₃₁ ∷ b₃₂ ∷ b₃₃ ∷ b₃₄ ∷ [])
    ∷ []

pad256To64₁ : (Binary 8) → Vec (Binary 6) 2
pad256To64₁ (b₁₁ ∷ b₁₂ ∷ b₁₃ ∷ b₁₄ ∷ b₁₅ ∷ b₁₆ ∷ b₁₇ ∷ b₁₈ ∷ []) =
  (  (b₁₁ ∷ b₁₂ ∷ b₁₃ ∷ b₁₄ ∷ b₁₅ ∷ Vec.[ b₁₆ ])
   ∷ Vec.[ b₁₇ ∷ b₁₈ ∷ Vec.replicate #0 ])

pad256To64₂ : ((Binary 8) × (Binary 8)) → Vec (Binary 6) 3
pad256To64₂ (  (b₁₁ ∷ b₁₂ ∷ b₁₃ ∷ b₁₄ ∷ b₁₅ ∷ b₁₆ ∷ b₁₇ ∷ b₁₈ ∷ [])
             , (b₂₁ ∷ b₂₂ ∷ b₂₃ ∷ b₂₄ ∷ b₂₅ ∷ b₂₆ ∷ b₂₇ ∷ b₂₈ ∷ []))
  = ( (b₁₁ ∷ b₁₂ ∷ b₁₃ ∷ b₁₄ ∷ b₁₅ ∷ Vec.[ b₁₆ ])
      ∷ (b₁₇ ∷ b₁₈ ∷ b₂₁ ∷ b₂₂ ∷ b₂₃ ∷ Vec.[ b₂₄ ])
      ∷ Vec.[ b₂₅ ∷ b₂₆ ∷ b₂₇ ∷ b₂₈ ∷ Vec.replicate #0 ])

