open import Armor.Binary.Base64EncDec.EncDec.Properties
open import Armor.Binary.Base64EncDec.EncDec.TCB
open import Armor.Prelude

module Armor.Binary.Base64EncDec.EncDec where

open import Armor.Binary.UInt6
open import Armor.Binary.UInt8

encode : List UInt8 → List UInt6
encode = base256To64

decode : (bs : List UInt6) → Valid64Encoding bs → List UInt8
decode bs v = proj₁ (base64To256Valid bs v)

encodeValid : (bs : List UInt8) → Valid64Encoding (encode bs)
encodeValid = base256To64Valid

decodeEncode : ∀ bs → (v : Valid64Encoding bs) → encode (decode bs v) ≡ bs
decodeEncode bs v = Maybe.just-injective (begin
  (just (encode (decode bs v)) ≡⟨⟩
  just (encode (proj₁ (base64To256Valid bs v))) ≡⟨⟩
  maybe′ (just ∘ encode) nothing (just (proj₁ (base64To256Valid bs v)))
    ≡⟨ cong (maybe′ (just ∘ encode) nothing)
         (sym $ proj₂ (base64To256Valid bs v)) ⟩
  maybe′ (just ∘ encode) nothing (base64To256 bs)
    ≡⟨ base256To64∘base64To256 bs v ⟩
  just bs ∎))

  where
  open ≡-Reasoning
  import Data.Maybe.Properties as Maybe

encodeDecode : ∀ bs → decode (encode bs) (encodeValid bs) ≡ bs
encodeDecode bs = Maybe.just-injective (begin
  (just (decode (encode bs) (encodeValid bs)) ≡⟨⟩
  just (proj₁ (base64To256Valid (encode bs) (encodeValid bs)))
    ≡⟨ (sym $ proj₂ (base64To256Valid (encode bs) (encodeValid bs))) ⟩
  base64To256 (base256To64 bs) ≡⟨ base64To256∘base256To64 bs ⟩
  just bs ∎))
  where
  open ≡-Reasoning
  import Data.Maybe.Properties as Maybe
