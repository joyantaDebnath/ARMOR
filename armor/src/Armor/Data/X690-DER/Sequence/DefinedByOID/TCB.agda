open import Armor.Binary
open import Armor.Data.X690-DER.OID.TCB
open import Armor.Data.X690-DER.TLV.TCB
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Definitions.Iso
import      Armor.Grammar.Definitions.NonMalleable
import      Armor.Grammar.Seq.TCB
open import Armor.Prelude

module Armor.Data.X690-DER.Sequence.DefinedByOID.TCB where

open Armor.Grammar.Definitions.Iso          UInt8
open Armor.Grammar.Definitions.NonMalleable UInt8
open Armor.Grammar.Seq.TCB                  UInt8

AnyDefinedByOID : Set₁
AnyDefinedByOID = {@0 bs : List UInt8} → OID bs → @0 List UInt8 → Set

record DefinedByOIDFields (P : AnyDefinedByOID) (@0 bs : List UInt8) : Set where
  constructor mkOIDDefinedFields
  field
    @0 {o p} : List UInt8
    oid : OID o
    param  : P oid p
    @0 bs≡ : bs ≡ o ++ p

DefinedByOIDFieldsRep : AnyDefinedByOID → @0 List UInt8 → Set
DefinedByOIDFieldsRep P = &ₚᵈ OID P

equivalent : {@0 P : AnyDefinedByOID} → Equivalent (DefinedByOIDFieldsRep P) (DefinedByOIDFields P)
proj₁ equivalent (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = mkOIDDefinedFields fstₚ₁ sndₚ₁ bs≡
proj₂ equivalent (mkOIDDefinedFields oid param bs≡) = mk&ₚ oid param bs≡

DefinedByOID : (P : AnyDefinedByOID) → @0 List UInt8 → Set
DefinedByOID P = TLV Tag.Sequence (DefinedByOIDFields P)

RawDefinedByOIDFields : {P : AnyDefinedByOID} → Raw₁ RawOID P → Raw (DefinedByOIDFields P)
RawDefinedByOIDFields r = Iso.raw equivalent (Raw&ₚᵈ RawOID r)

RawDefinedByOID : {P : AnyDefinedByOID} → Raw₁ RawOID P → Raw (DefinedByOID P)
RawDefinedByOID r = RawTLV _ (RawDefinedByOIDFields r)
