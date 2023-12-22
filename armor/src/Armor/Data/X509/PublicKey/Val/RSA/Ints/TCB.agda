open import Armor.Binary
open import Armor.Data.X690-DER.Int.TCB
open import Armor.Data.X690-DER.TLV.TCB
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Definitions.Iso
import      Armor.Grammar.Definitions.NonMalleable
import      Armor.Grammar.Seq.TCB
open import Armor.Prelude

module Armor.Data.X509.PublicKey.Val.RSA.Ints.TCB where

open Armor.Grammar.Definitions.Iso          UInt8
open Armor.Grammar.Definitions.NonMalleable UInt8
open Armor.Grammar.Seq.TCB                  UInt8

record RSAPkIntsFields (@0 bs : List UInt8) : Set where
  constructor mkRSAPkIntsFields
  field
    @0 {n e} : List UInt8
    nval : Int n 
    eval : Int e
    @0 bs≡ : bs ≡ n ++ e

RSAPkIntsFieldsRep : @0 List UInt8 → Set
RSAPkIntsFieldsRep = &ₚ Int Int

equivalent : Equivalent RSAPkIntsFieldsRep RSAPkIntsFields
proj₁ equivalent (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = mkRSAPkIntsFields fstₚ₁ sndₚ₁ bs≡
proj₂ equivalent (mkRSAPkIntsFields nval eval bs≡) = mk&ₚ nval eval bs≡

RawRSAPkIntsFieldsRep : Raw RSAPkIntsFieldsRep
RawRSAPkIntsFieldsRep = Raw&ₚ RawInt RawInt

RawRSAPkIntsFields : Raw RSAPkIntsFields
RawRSAPkIntsFields = Iso.raw equivalent RawRSAPkIntsFieldsRep

RSAPkInts : @0 List UInt8 → Set
RSAPkInts xs = TLV Tag.Sequence RSAPkIntsFields xs

RawRSAPkInts : Raw RSAPkInts
RawRSAPkInts = RawTLV _ RawRSAPkIntsFields
