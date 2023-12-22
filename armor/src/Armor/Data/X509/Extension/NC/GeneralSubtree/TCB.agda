open import Armor.Binary
open import Armor.Data.X509.GeneralNames.GeneralName.TCB
open import Armor.Data.X690-DER.Default.TCB
open import Armor.Data.X690-DER.Int.TCB
open import Armor.Data.X690-DER.Int.Properties
open import Armor.Data.X690-DER.Length.TCB
open import Armor.Data.X690-DER.TLV.TCB
open import Armor.Data.X690-DER.TLV.Properties
import      Armor.Data.X690-DER.Tag as Tag
open import Armor.Data.X690-DER.SequenceOf.TCB
import      Armor.Grammar.Option
import      Armor.Grammar.Definitions
import      Armor.Grammar.Seq.TCB
open import Armor.Prelude

module Armor.Data.X509.Extension.NC.GeneralSubtree.TCB where

open Armor.Grammar.Option UInt8
open Armor.Grammar.Definitions              UInt8
open Armor.Grammar.Seq.TCB UInt8

{- https://datatracker.ietf.org/doc/html/rfc5280#section-4.2.1.10
-- 
--    GeneralSubtrees ::= SEQUENCE SIZE (1..MAX) OF GeneralSubtree
--
--    GeneralSubtree ::= SEQUENCE {
--         base                    GeneralName,
--         minimum         [0]     BaseDistance DEFAULT 0,
--         maximum         [1]     BaseDistance OPTIONAL }
--
--    BaseDistance ::= INTEGER (0..MAX)
-}

MinBaseDistance : @0 List UInt8 → Set
MinBaseDistance = [ Tag.A80 ]Int

MaxBaseDistance : @0 List UInt8 → Set
MaxBaseDistance = [ Tag.A81 ]Int

defaultMinBaseDistance : MinBaseDistance _
defaultMinBaseDistance = mkTLV (short (mkShort (# 1) (toWitness{Q = _ <? _} tt) refl))
  (mkIntVal (# 0) [] tt self refl) refl refl

record GeneralSubtreeFields (@0 bs : List UInt8) : Set where
  constructor mkGeneralSubtreeFields
  field
    @0 {bse minb maxb} : List UInt8
    base : GeneralName bse
    minimum : Default MinBaseDistance defaultMinBaseDistance minb
    maximum : Option MaxBaseDistance maxb
    @0 bs≡  : bs ≡ bse ++ minb ++ maxb

GeneralSubtree : @0 List UInt8 → Set
GeneralSubtree xs = TLV Tag.Sequence GeneralSubtreeFields xs

GeneralSubtrees : @0 List UInt8 → Set
GeneralSubtrees xs = (NonEmptySequenceOf GeneralSubtree) xs

GeneralSubtreeFieldsRep = &ₚ GeneralName (&ₚ (Default MinBaseDistance defaultMinBaseDistance) (Option MaxBaseDistance))

equivalentGeneralSubtreeFields : Equivalent GeneralSubtreeFieldsRep GeneralSubtreeFields
proj₁ equivalentGeneralSubtreeFields (mk&ₚ fstₚ₁ (mk&ₚ fstₚ₂ sndₚ₁ refl) refl) = mkGeneralSubtreeFields fstₚ₁ fstₚ₂ sndₚ₁ refl
proj₂ equivalentGeneralSubtreeFields (mkGeneralSubtreeFields base minimum maximum refl) = (mk&ₚ base (mk&ₚ minimum maximum refl) refl)

RawGeneralSubtreeFieldsRep : Raw GeneralSubtreeFieldsRep
RawGeneralSubtreeFieldsRep = Raw&ₚ RawGeneralName
                              (Raw&ₚ (RawDefault (RawTLV _ RawIntegerValue) defaultMinBaseDistance)
                                      (RawOption (RawTLV _ RawIntegerValue)))

RawGeneralSubtreeFields : Raw GeneralSubtreeFields
RawGeneralSubtreeFields = Iso.raw equivalentGeneralSubtreeFields RawGeneralSubtreeFieldsRep

RawGeneralSubtrees : Raw GeneralSubtrees
RawGeneralSubtrees = RawBoundedSequenceOf (RawTLV _ RawGeneralSubtreeFields) 1
