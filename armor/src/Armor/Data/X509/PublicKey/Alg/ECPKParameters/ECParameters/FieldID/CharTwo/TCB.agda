open import Armor.Binary
open import Armor.Data.X509.PublicKey.Alg.ECPKParameters.ECParameters.FieldID.CharTwo.Basis.TCB
open import Armor.Data.X690-DER.Int.TCB
open import Armor.Data.X690-DER.TLV.TCB
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Definitions.Iso
import      Armor.Grammar.Definitions.NonMalleable
import      Armor.Grammar.Seq.TCB
open import Armor.Prelude

module Armor.Data.X509.PublicKey.Alg.ECPKParameters.ECParameters.FieldID.CharTwo.TCB where

open Armor.Grammar.Definitions.Iso          UInt8
open Armor.Grammar.Definitions.NonMalleable UInt8
open Armor.Grammar.Seq.TCB                  UInt8

{- https://datatracker.ietf.org/doc/html/rfc3279#section-2.3.5
-- The object identifiers prime-field and characteristic-two-field name
-- the two kinds of fields defined in this Standard.  They have the
-- following values:
--   Characteristic-two ::= SEQUENCE {
--       m           INTEGER,                      -- Field size 2^m
--       basis       OBJECT IDENTIFIER,
--       parameters  ANY DEFINED BY basis }
--
-}

record CharTwoFields (@0 bs : List UInt8) : Set where
  constructor mkCharTwoFields
  field
    @0 {bs₁ bs₂} : List UInt8
    m : Int bs₁
    basis : BasisFields bs₂
    @0 bs≡ : bs ≡ bs₁ ++ bs₂

CharTwoFieldsRep : @0 List UInt8 → Set
CharTwoFieldsRep = &ₚ Int BasisFields

equivalent : Equivalent CharTwoFieldsRep CharTwoFields
proj₁ equivalent (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = mkCharTwoFields fstₚ₁ sndₚ₁ bs≡
proj₂ equivalent (mkCharTwoFields m basis bs≡) = mk&ₚ m basis bs≡

RawCharTwoFieldsRep : Raw CharTwoFieldsRep
RawCharTwoFieldsRep = Raw&ₚ RawInt RawBasisFields

RawCharTwoFields : Raw CharTwoFields
RawCharTwoFields = Iso.raw equivalent RawCharTwoFieldsRep

CharTwo = TLV Tag.Sequence CharTwoFields

RawCharTwo : Raw CharTwo
RawCharTwo = RawTLV _ RawCharTwoFields
