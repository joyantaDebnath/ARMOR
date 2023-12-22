open import Armor.Binary
open import Armor.Data.X509.Extension.NC.GeneralSubtree.TCB
open import Armor.Data.X690-DER.TLV.TCB
import      Armor.Data.X690-DER.Tag as Tag
open import Armor.Data.X690-DER.SequenceOf.TCB
import      Armor.Grammar.Option
import      Armor.Grammar.Definitions
import      Armor.Grammar.Seq.TCB
open import Armor.Prelude

module Armor.Data.X509.Extension.NC.TCB where

open      Armor.Grammar.Definitions              UInt8

open Armor.Grammar.Option UInt8
open Armor.Grammar.Seq.TCB UInt8

-- https://datatracker.ietf.org/doc/html/rfc5280#section-4.2.1.10
--       id-ce-nameConstraints OBJECT IDENTIFIER ::=  { id-ce 30 }

--       NameConstraints ::= SEQUENCE {
--            permittedSubtrees       [0]     GeneralSubtrees OPTIONAL,
--            excludedSubtrees        [1]     GeneralSubtrees OPTIONAL }

--       GeneralSubtrees ::= SEQUENCE SIZE (1..MAX) OF GeneralSubtree

--       GeneralSubtree ::= SEQUENCE {
--            base                    GeneralName,
--            minimum         [0]     BaseDistance DEFAULT 0,
--            maximum         [1]     BaseDistance OPTIONAL }

--       BaseDistance ::= INTEGER (0..MAX)
      
PermittedSubtrees : @0 List UInt8 → Set
PermittedSubtrees xs = TLV Tag.AA0 GeneralSubtrees xs

ExcludedSubtrees : @0 List UInt8 → Set
ExcludedSubtrees xs = TLV Tag.AA1 GeneralSubtrees xs

record NCFieldsSeqFields (@0 bs : List UInt8) : Set where
  constructor mkNCFieldsSeqFields
  field
    @0 {pe ex} : List UInt8
    permt : Option PermittedSubtrees pe
    excld : Option ExcludedSubtrees ex
    @0 bs≡  : bs ≡ pe ++ ex

NCFieldsSeq : @0 List UInt8 → Set
NCFieldsSeq xs = TLV Tag.Sequence NCFieldsSeqFields xs

NCFields : @0 List UInt8 → Set
NCFields xs = TLV Tag.OctetString  NCFieldsSeq xs

NCFieldsSeqFieldsRep = &ₚ (Option PermittedSubtrees) (Option ExcludedSubtrees)

equivalentNCFieldsSeqFields : Equivalent NCFieldsSeqFieldsRep NCFieldsSeqFields
proj₁ equivalentNCFieldsSeqFields (mk&ₚ fstₚ₁ sndₚ₁ refl) = mkNCFieldsSeqFields fstₚ₁ sndₚ₁ refl
proj₂ equivalentNCFieldsSeqFields (mkNCFieldsSeqFields permt excld refl) = mk&ₚ permt excld refl

RawNCFieldsSeqFieldsRep : Raw NCFieldsSeqFieldsRep
RawNCFieldsSeqFieldsRep = Raw&ₚ (RawOption (RawTLV _ RawGeneralSubtrees)) (RawOption (RawTLV _ RawGeneralSubtrees))

RawNCFieldsSeqFields : Raw NCFieldsSeqFields
RawNCFieldsSeqFields = Iso.raw equivalentNCFieldsSeqFields RawNCFieldsSeqFieldsRep

RawNCFields : Raw NCFields
RawNCFields = RawTLV _ (RawTLV _ RawNCFieldsSeqFields)
