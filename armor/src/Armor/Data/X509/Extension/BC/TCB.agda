open import Armor.Binary
open import Armor.Data.X690-DER.Boool.TCB
open import Armor.Data.X690-DER.Boool.Eq
open import Armor.Data.X690-DER.Default.TCB
open import Armor.Data.X690-DER.Int.TCB
open import Armor.Data.X690-DER.Length.TCB
open import Armor.Data.X690-DER.TLV.TCB
open import Armor.Data.X690-DER.TLV.Properties
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Option
import      Armor.Grammar.Definitions
import      Armor.Grammar.Seq.TCB
open import Armor.Prelude

module Armor.Data.X509.Extension.BC.TCB where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Option UInt8
open Armor.Grammar.Seq.TCB UInt8

-- https://datatracker.ietf.org/doc/html/rfc5280#section-4.2.1.9
--    id-ce-basicConstraints OBJECT IDENTIFIER ::=  { id-ce 19 }

--    BasicConstraints ::= SEQUENCE {
--         cA                      BOOLEAN DEFAULT FALSE,
--         pathLenConstraint       INTEGER (0..MAX) OPTIONAL }

record BCFieldsSeqFields (@0 bs : List UInt8) : Set where
  constructor mkBCFieldsSeqFields
  field
    @0 {ca pl} : List UInt8
    bcca : Default Boool falseBoool ca
    bcpathlen : Option Int pl
    @0 bs≡  : bs ≡ ca ++ pl

  isCA : Bool
  isCA = BoolValue.v ∘ TLV.val ∘ proj₂ ∘ Default.getValue $ bcca

BCFieldsSeq : @0 List UInt8 → Set
BCFieldsSeq xs = TLV Tag.Sequence  BCFieldsSeqFields xs

BCFields : @0 List UInt8 → Set
BCFields xs = TLV Tag.OctetString  BCFieldsSeq xs

isCA : ∀ {@0 bs} → BCFields bs → Bool
isCA bcf = BCFieldsSeqFields.isCA (TLV.val (TLV.val bcf))

BCFieldsSeqFieldsRep = &ₚ (Default Boool falseBoool) (Option Int)

equivalentBCFieldsSeqFields : Equivalent BCFieldsSeqFieldsRep BCFieldsSeqFields
proj₁ equivalentBCFieldsSeqFields (Armor.Grammar.Seq.TCB.mk&ₚ fstₚ₁ sndₚ₁ bs≡) = mkBCFieldsSeqFields fstₚ₁ sndₚ₁ bs≡
proj₂ equivalentBCFieldsSeqFields (mkBCFieldsSeqFields bcca bcpathlen bs≡) = Armor.Grammar.Seq.TCB.mk&ₚ bcca bcpathlen bs≡

RawBCFieldsSeqFieldsRep : Raw BCFieldsSeqFieldsRep
RawBCFieldsSeqFieldsRep = Raw&ₚ (RawDefault RawBoool falseBoool) (RawOption RawInt)

RawBCFieldsSeqFields : Raw BCFieldsSeqFields
RawBCFieldsSeqFields = Iso.raw equivalentBCFieldsSeqFields RawBCFieldsSeqFieldsRep

RawBCFields : Raw BCFields
RawBCFields = RawTLV _ (RawTLV _  RawBCFieldsSeqFields)
