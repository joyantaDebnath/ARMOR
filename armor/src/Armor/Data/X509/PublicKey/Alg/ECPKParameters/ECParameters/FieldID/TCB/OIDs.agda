open import Armor.Binary
open import Armor.Data.X690-DER.OID
import      Armor.Grammar.Parallel
import      Armor.Grammar.Parser
open import Armor.Prelude

module Armor.Data.X509.PublicKey.Alg.ECPKParameters.ECParameters.FieldID.TCB.OIDs where

open Armor.Grammar.Parallel UInt8
open Armor.Grammar.Parser   UInt8

{- https://datatracker.ietf.org/doc/html/rfc3279#section-3
--
--    ansi-X9-62 OBJECT IDENTIFIER ::= {
--       iso(1) member-body(2) us(840) 10045 }
--    id-fieldType OBJECT IDENTIFIER ::= { ansi-X9-62 fieldType(1) }
--
-- https://datatracker.ietf.org/doc/html/rfc3279#section-2.3.5
--
-- The object identifiers prime-field and characteristic-two-field name
-- the two kinds of fields defined in this Standard.  They have the
-- following values:
--
--    prime-field OBJECT IDENTIFIER ::= { id-fieldType 1 }
--    characteristic-two-field OBJECT IDENTIFIER ::= { id-fieldType 2 }
-}
ANSI-X9-62-Arc FieldTypeArc PrimeFieldLit CharTwoFieldLit : List UInt8

ANSI-X9-62-Arc = # 42 ∷ # 134 ∷ # 72 ∷ # 206 ∷ [ # 61 ]
FieldTypeArc    = ANSI-X9-62-Arc ++ [ # 1 ]
PrimeFieldLit   = FieldTypeArc ++ [ # 1 ]
CharTwoFieldLit = FieldTypeArc ++ [ # 2 ]

PrimeField : OIDValue PrimeFieldLit
PrimeField = fstₚ (Success.value (toWitness{Q = Logging.val (runParser (parseOIDValue (length PrimeFieldLit)) PrimeFieldLit)} tt))

CharTwoField : OIDValue CharTwoFieldLit
CharTwoField = fstₚ (Success.value (toWitness{Q = Logging.val (runParser (parseOIDValue (length CharTwoFieldLit)) CharTwoFieldLit)} tt))

Supported : List (Exists─ _ OIDValue)
Supported = (-, PrimeField) ∷ [ -, CharTwoField ]
