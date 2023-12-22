open import Armor.Binary
import      Armor.Data.X509.PublicKey.Alg.ECPKParameters.ECParameters.FieldID.TCB.OIDs as FieldID
open import Armor.Data.X690-DER.OID
import      Armor.Grammar.Parallel
import      Armor.Grammar.Parser
open import Armor.Prelude

module Armor.Data.X509.PublicKey.Alg.ECPKParameters.ECParameters.FieldID.CharTwo.Basis.TCB.OIDs where

open Armor.Grammar.Parallel UInt8
open Armor.Grammar.Parser   UInt8

{- https://datatracker.ietf.org/doc/html/rfc3279#section-2.3.5
-- The object identifier id-characteristic-two-basis specifies an arc
-- containing the object identifiers for each type of basis for the
-- characteristic-two finite fields.  It has the following value:
--
--    id-characteristic-two-basis OBJECT IDENTIFIER ::= {
--         characteristic-two-field basisType(1) }
--
-- The object identifiers gnBasis, tpBasis and ppBasis name the three
-- kinds of basis for characteristic-two finite fields defined by
-- [X9.62].  They have the following values:
--
--    gnBasis OBJECT IDENTIFIER ::= { id-characteristic-two-basis 1 }
--
--    -- for gnBasis, the value of the parameters field is NULL
--
--    tpBasis OBJECT IDENTIFIER ::= { id-characteristic-two-basis 2 }
--
--    -- type of parameters field for tpBasis is Trinomial
--
--    Trinomial ::= INTEGER
--
--    ppBasis OBJECT IDENTIFIER ::= { id-characteristic-two-basis 3 }
--
--    -- type of parameters field for ppBasis is Pentanomial
--
--    Pentanomial ::= SEQUENCE {
--       k1  INTEGER,
--       k2  INTEGER,
--       k3  INTEGER }
-}

BasisTypeArc GNBasisLit TPBasisLit PPBasisLit : List UInt8

BasisTypeArc = FieldID.CharTwoFieldLit ++ [ # 1 ]

GNBasisLit = BasisTypeArc ++ [ # 1 ]
TPBasisLit = BasisTypeArc ++ [ # 2 ]
PPBasisLit = BasisTypeArc ++ [ # 3 ]

GNBasis : OIDValue GNBasisLit
GNBasis = fstₚ (Success.value (toWitness{Q = Logging.val (runParser (parseOIDValue (length GNBasisLit)) GNBasisLit)} tt))

TPBasis : OIDValue TPBasisLit
TPBasis = fstₚ (Success.value (toWitness{Q = Logging.val (runParser (parseOIDValue (length TPBasisLit)) TPBasisLit)} tt))

PPBasis : OIDValue PPBasisLit
PPBasis = fstₚ (Success.value (toWitness{Q = Logging.val (runParser (parseOIDValue (length PPBasisLit)) PPBasisLit)} tt))

Supported : List (Exists─ (List UInt8) OIDValue)
Supported = (-, GNBasis) ∷ (-, TPBasis) ∷ [ -, PPBasis ]
