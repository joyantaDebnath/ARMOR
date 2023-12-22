open import Armor.Binary
import      Armor.Data.X509.PublicKey.Alg.ECPKParameters.ECParameters.FieldID.TCB.OIDs as OIDs
open import Armor.Data.X509.PublicKey.Alg.ECPKParameters.ECParameters.FieldID.CharTwo.TCB
  hiding (equivalent)
open import Armor.Data.X690-DER.Int.TCB
open import Armor.Data.X690-DER.OID
open import Armor.Data.X690-DER.TLV.TCB
open import Armor.Data.X690-DER.Sequence.DefinedByOID.TCB
import      Armor.Grammar.Definitions.NonMalleable
import      Armor.Grammar.Sum.TCB
open import Armor.Prelude

module Armor.Data.X509.PublicKey.Alg.ECPKParameters.ECParameters.FieldID.TCB where

open Armor.Grammar.Definitions.NonMalleable UInt8
open Armor.Grammar.Sum.TCB                  UInt8

{- https://datatracker.ietf.org/doc/html/rfc3279#section-2.3.5
--       FieldID ::= SEQUENCE {
--       fieldType   OBJECT IDENTIFIER,
--       parameters  ANY DEFINED BY fieldType }
--
-- FieldID is a SEQUENCE of two components, fieldType and parameters.
-- The fieldType contains an object identifier value that uniquely
-- identifies the type contained in the parameters.
--
-- The object identifiers prime-field and characteristic-two-field name
-- the two kinds of fields defined in this Standard.  They have the
-- following values:
--
--    prime-field OBJECT IDENTIFIER ::= { id-fieldType 1 }
--
--    Prime-p ::= INTEGER    -- Field size p (p in bits)
--
--    characteristic-two-field OBJECT IDENTIFIER ::= { id-fieldType 2 }
--
--    Characteristic-two ::= SEQUENCE {
--       m           INTEGER,                      -- Field size 2^m
--       basis       OBJECT IDENTIFIER,
--       parameters  ANY DEFINED BY basis }
-}

FieldIDParameters' : ∀ {@0 bs} (o : OID bs) → Dec ((-, TLV.val o) ∈ OIDs.Supported) → @0 List UInt8 → Set
FieldIDParameters' o (no ¬p) bs = ⊥
FieldIDParameters' o (yes (here px)) bs = Int bs
FieldIDParameters' o (yes (there (here px))) bs = CharTwo bs

FieldIDParameters : AnyDefinedByOID
FieldIDParameters o = FieldIDParameters' o ((-, TLV.val o) ∈? OIDs.Supported)

RawFieldIDParameters“ : Raw (Sum Int CharTwo)
RawFieldIDParameters“ = RawSum RawInt RawCharTwo

RawFieldIDParameters : Raw₁ RawOID FieldIDParameters
toRawFieldIDParameters : ∀ {@0 bs} → (o : OID bs) (o∈? : Dec ((-, TLV.val o) ∈ OIDs.Supported)) → ∀ {@0 bs'} → FieldIDParameters' o o∈? bs' → Raw₁.D RawFieldIDParameters (Raw.to RawOID o)

Raw₁.D RawFieldIDParameters o = Raw.D RawFieldIDParameters“
Raw₁.to RawFieldIDParameters o = toRawFieldIDParameters o ((-, TLV.val o) ∈? OIDs.Supported)

toRawFieldIDParameters o (yes (here px)) p = Raw.to RawFieldIDParameters“ (Sum.inj₁ p)
toRawFieldIDParameters o (yes (there (here px))) p = Raw.to RawFieldIDParameters“ (Sum.inj₂ p)

FieldID : @0 List UInt8 → Set
FieldID = DefinedByOID FieldIDParameters

RawFieldID : Raw FieldID
RawFieldID = RawDefinedByOID RawFieldIDParameters
