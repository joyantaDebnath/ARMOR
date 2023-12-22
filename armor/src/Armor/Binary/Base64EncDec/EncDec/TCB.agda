import      Armor.Binary.Base64EncDec.Base64           as Base64
import      Armor.Binary.Base64EncDec.EncDec.Bytes.TCB as Bytes
open import Armor.Binary.Bits.TCB
open import Armor.Binary.UInt6
open import Armor.Binary.UInt8.TCB
open import Armor.Prelude

module Armor.Binary.Base64EncDec.EncDec.TCB where

Valid64Encoding : List UInt6 → Set
Valid64Encoding [] = ⊤
Valid64Encoding (x ∷ []) = ⊥
Valid64Encoding (x ∷ x₁ ∷ []) = Vec.drop 2 {4} (toBinary{6} x₁) ≡ Vec.replicate #0
Valid64Encoding (x ∷ x₁ ∷ x₂ ∷ []) = Vec.drop 4 {2} (toBinary{6} x₂) ≡ Vec.replicate #0
Valid64Encoding (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ bs) = Valid64Encoding bs

base64To256 : List UInt6 → Maybe (List UInt8)
base64To256 [] = just []
base64To256 (x ∷ []) = nothing
  -- a single base64 digit is not enough to encode a base256 digi
base64To256 (c₀ ∷ c₁ ∷ []) = do
  let bs = Bytes.pad64To256 (Base64.pad2 (toBinary c₀ ∷ toBinary c₁ ∷ []))
  return (map fromBinary bs)
base64To256 (c₀ ∷ c₁ ∷ c₂ ∷ []) = do
  let bs = Bytes.pad64To256 (Base64.pad1 (toBinary c₀ ∷ toBinary c₁ ∷ toBinary c₂ ∷ []))
  return (map fromBinary bs)
base64To256 (c₀ ∷ c₁ ∷ c₂ ∷ c₃ ∷ cs) = do
  let bs = Bytes.base64To256 (toBinary c₀ ∷ toBinary c₁ ∷ toBinary c₂ ∷ toBinary c₃ ∷ [])
  ds ← base64To256 cs
  return (map fromBinary (Vec.toList bs) ++ ds)

-- encode : List UInt8 -> List UInt6
base256To64 : List UInt8 → List UInt6
base256To64 [] = []
base256To64 (x ∷ []) = map fromBinary (Vec.toList (Bytes.pad256To64₁ (toBinary x)))
base256To64 (x ∷ x₁ ∷ []) =
  map fromBinary (Vec.toList (Bytes.pad256To64₂ (toBinary x , toBinary x₁)))
base256To64 (x ∷ x₁ ∷ x₂ ∷ xs) =
  let bs = Bytes.base256To64 (Vec.map toBinary (x ∷ x₁ ∷ Vec.[ x₂ ]))
  in
  map fromBinary (Vec.toList bs) ++ base256To64 xs
