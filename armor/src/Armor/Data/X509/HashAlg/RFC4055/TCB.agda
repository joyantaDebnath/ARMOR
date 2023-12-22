open import Armor.Binary
import      Armor.Data.X509.HashAlg.TCB.OIDs as OIDs
open import Armor.Data.X690-DER.Null.TCB
open import Armor.Data.X690-DER.OID
open import Armor.Data.X690-DER.Sequence.DefinedByOID.TCB
open import Armor.Data.X690-DER.TLV.TCB
import      Armor.Grammar.Definitions.Iso
import      Armor.Grammar.Definitions.NonMalleable
import      Armor.Grammar.Option.TCB
open import Armor.Prelude

module Armor.Data.X509.HashAlg.RFC4055.TCB where

open Armor.Grammar.Definitions.Iso          UInt8
open Armor.Grammar.Definitions.NonMalleable UInt8
open Armor.Grammar.Option.TCB              UInt8

HashAlgParam' : ∀ {@0 bs} → (o : OID bs) (o∈? : Dec ((-, TLV.val o) ∈ OIDs.RFC4055)) → @0 List UInt8 → Set
HashAlgParam' o (no ¬p) = λ _ → ⊥
HashAlgParam' o (yes p) = Option Null

HashAlgParam : ∀ {@0 bs} → OID bs → @0 List UInt8 → Set
HashAlgParam o = HashAlgParam' o ((-, TLV.val o) ∈? OIDs.RFC4055)

HashAlgParamRep : @0 List UInt8 → Set
HashAlgParamRep = Option Null

RawHashAlgParamRep : Raw HashAlgParamRep
RawHashAlgParamRep = RawOption RawNull

RawHashAlgParam : Raw₁ RawOID HashAlgParam
toRawHashAlgParam : ∀ {@0 bs} → (o : OID bs) (o∈? : Dec ((-, TLV.val o) ∈ OIDs.RFC4055))
                    → ∀ {@0 bs'} → HashAlgParam' o o∈? bs' → Raw₁.D RawHashAlgParam (Raw.to RawOID o)

Raw₁.D RawHashAlgParam o = Raw.D RawHashAlgParamRep
Raw₁.to RawHashAlgParam o = toRawHashAlgParam o ((-, TLV.val o) ∈? OIDs.RFC4055)

toRawHashAlgParam o (yes p₁) p = Raw.to RawHashAlgParamRep p

HashAlg : @0 List UInt8 → Set
HashAlg = DefinedByOID HashAlgParam

RawHashAlg : Raw HashAlg
RawHashAlg = RawDefinedByOID RawHashAlgParam
