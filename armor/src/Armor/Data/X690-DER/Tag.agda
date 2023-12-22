open import Armor.Binary
open import Armor.Prelude
import      Data.Nat.Properties as Nat
  
module Armor.Data.X690-DER.Tag where

Boolean : UInt8
Boolean = # 1

Integer : UInt8
Integer = # 2

BitString : UInt8
BitString = # 3

OctetString : UInt8
OctetString = # 4

Null : UInt8
Null = # 5

ObjectIdentifier : UInt8
ObjectIdentifier = # 6

UTF8String : UInt8
UTF8String = # 12

-- Character string types
PrintableString : UInt8
PrintableString = # 19

TeletexString : UInt8
TeletexString = # 20

IA5String : UInt8
IA5String = # 22

UTCTime : UInt8
UTCTime = # 23

GeneralizedTime : UInt8
GeneralizedTime = # 24

-- Character string types (cont.)
VisibleString : UInt8
VisibleString = # 26

UniversalString : UInt8
UniversalString = # 28

BMPString : UInt8
BMPString = # 30

Sequence : UInt8
Sequence = # 48

Sett : UInt8
Sett = # 49

-- 8x
AppPrim : (n : ℕ) {wit : True (n <? 16)} → UInt8
AppPrim n {wit} = Fin.fromℕ< ∘ s≤s $ begin
  128 + n <⟨ Nat.+-monoʳ-< 128 (toWitness wit) ⟩
  144 ≤⟨ toWitness{Q = 144 ≤? 255} tt ⟩
  255 ∎
  where open Nat.≤-Reasoning

A80 = AppPrim 0
A81 = AppPrim 1
A82 = AppPrim 2
A86 = AppPrim 6
A87 = AppPrim 7
A88 = AppPrim 8

-- Ax
AppCon : (n : ℕ) {wit : True (n <? 16)} → UInt8
AppCon n {wit} = Fin.fromℕ< ∘ s≤s $ begin
  160 + n <⟨ Nat.+-monoʳ-< 160 (toWitness wit) ⟩
  176 ≤⟨ toWitness{Q = 176 ≤? 255} tt ⟩
  255 ∎
  where open Nat.≤-Reasoning

AA0 = AppCon 0
AA1 = AppCon 1
AA2 = AppCon 2
AA3 = AppCon 3
AA4 = AppCon 4
AA5 = AppCon 5

