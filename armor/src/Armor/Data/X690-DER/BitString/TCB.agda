open import Armor.Binary
open import Armor.Data.X690-DER.TLV
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Definitions.NonMalleable
open import Armor.Prelude

module Armor.Data.X690-DER.BitString.TCB where

open Armor.Grammar.Definitions.NonMalleable UInt8

-- https://www.itu.int/rec/T-REC-X.690-202102-I/en
-- 8.6.2 The contents octets for the primitive encoding shall contain an initial octet followed by zero, one or more subsequent
-- octets.
-- 8.6.2.1 The bits in the bitstring value, commencing with the leading bit and proceeding to the trailing bit, shall be placed in
-- bits 8 to 1 of the first subsequent octet, followed by bits 8 to 1 of the second subsequent octet, followed by bits 8 to 1 of each
-- octet in turn, followed by as many bits as are needed of the final subsequent octet, commencing with bit 8.
-- NOTE – The terms "leading bit" and "trailing bit" are defined in Rec. ITU-T X.680 | ISO/IEC 8824-1, 22.2.
-- 8.6.2.2 The initial octet shall encode, as an unsigned binary integer with bit 1 as the least significant bit, the number of
-- unused bits in the final subsequent octet. The number shall be in the range zero to seven.
-- 8.6.2.3 If the bitstring is empty, there shall be no subsequent octets, and the initial octet shall be zero.
-- 11.2.1 Each unused bit in the final octet of the encoding of a bit string value shall be set to zero.
-- 11.2.2 Where Rec. ITU-T X.680 | ISO/IEC 8824-1, 22.7, applies, the bitstring shall have all trailing 0 bits removed before
-- it is encoded.
-- NOTE 1 – In the case where a size constraint has been applied, the abstract value delivered by a decoder to the application will be one
-- of those satisfying the size constraint and differing from the transmitted value only in the number of trailing 0 bits.
-- NOTE 2 – If a bitstring value has no 1 bits, then an encoder shall encode the value with a length of 1 and an initial octet set to 0.

UnusedBits : UInt8 → List UInt8 → Set
UnusedBits bₕ [] = toℕ bₕ ≡ 0
UnusedBits bₕ (bₜ ∷ []) = drop (8 - toℕ bₕ) (Vec.toList (toBinary{8} bₜ)) ≡ replicate (toℕ bₕ) #0
UnusedBits bₕ (bₜ ∷ x ∷ bₜ') = UnusedBits bₕ (x ∷ bₜ')

toBitRep : UInt8 → List UInt8 → List Bool
toBitRep bₕ [] = []
toBitRep bₕ (bₜ ∷ [])= take (8 - toℕ bₕ) (Vec.toList{n = 8} (toBinary bₜ))
toBitRep bₕ (bₜ ∷ x ∷ bₜ') = Vec.toList{n = 8} (toBinary bₜ) ++ toBitRep bₕ (x ∷ bₜ')

record BitStringValue (@0 bs : List UInt8) : Set where
    constructor mkBitStringValue
    field
      @0 bₕ : UInt8
      @0 bₜ : List UInt8
      @0 bₕ<8 : toℕ bₕ < 8
      bits : Singleton (toBitRep bₕ bₜ)
      @0 unusedBits : UnusedBits bₕ bₜ
      @0 bs≡ : bs ≡ bₕ ∷ bₜ

BitString : @0 List UInt8 → Set
BitString = TLV Tag.BitString BitStringValue

RawBitStringValue : Raw BitStringValue
Raw.D RawBitStringValue = List Bool
Raw.to RawBitStringValue = ↑_ ∘ BitStringValue.bits

RawBitString : Raw BitString
RawBitString = RawTLV _ RawBitStringValue
