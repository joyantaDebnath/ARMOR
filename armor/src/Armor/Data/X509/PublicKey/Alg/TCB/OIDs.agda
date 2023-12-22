open import Armor.Binary
import      Armor.Data.X690-DER.Tag as Tag
open import Armor.Data.X690-DER.OID
import      Armor.Grammar.Parallel.TCB
import      Armor.Grammar.Parser
open import Armor.Prelude

module Armor.Data.X509.PublicKey.Alg.TCB.OIDs where

open Armor.Grammar.Parallel.TCB UInt8
open Armor.Grammar.Parser       UInt8

{- https://datatracker.ietf.org/doc/html/rfc3279#section-2.3.1
-- The OID rsaEncryption identifies RSA public keys.
--
--    pkcs-1 OBJECT IDENTIFIER ::= { iso(1) member-body(2) us(840)
--                   rsadsi(113549) pkcs(1) 1 }
--
--    rsaEncryption OBJECT IDENTIFIER ::=  { pkcs-1 1}
--
-- The rsaEncryption OID is intended to be used in the algorithm field
-- of a value of type AlgorithmIdentifier.  The parameters field MUST
-- have ASN.1 type NULL for this algorithm identifier.
-}

RSALit : List UInt8
RSALit = # 42 ∷ # 134 ∷ # 72 ∷ # 134 ∷ # 247 ∷ # 13 ∷ # 1 ∷ # 1 ∷ [ # 1 ]

RSA : OIDValue RSALit
RSA = fstₚ (Success.value (toWitness{Q = Logging.val (runParser (parseOIDValue (length RSALit)) RSALit)} tt))

{- https://datatracker.ietf.org/doc/html/rfc3279#section-2.3.5
-- ECDH is the elliptic curve mathematical analog of the Diffie-Hellman
-- key agreement algorithm as specified in [X9.42].  The ECDSA and ECDH
-- specifications use the same OIDs and parameter encodings.  The ASN.1
-- object identifiers used to identify these public keys are defined in
-- the following arc:
--
-- ansi-X9-62 OBJECT IDENTIFIER ::=
--                           { iso(1) member-body(2) us(840) 10045 }
--
-- When certificates contain an ECDSA or ECDH public key, the
-- id-ecPublicKey algorithm identifier MUST be used. The id-ecPublicKey
-- algorithm identifier is defined as follows:
--
--   id-public-key-type OBJECT IDENTIFIER  ::= { ansi-X9.62 2 }
--
--   id-ecPublicKey OBJECT IDENTIFIER ::= { id-publicKeyType 1 }
--
-- This OID is used in public key certificates for both ECDSA signature
-- keys and ECDH encryption keys.  The intended application for the key
-- may be indicated in the key usage field (see [RFC 3280]).  The use of
-- a single key for both signature and encryption purposes is not
-- recommended, but is not forbidden.
-}

ECLit : List UInt8
ECLit = # 42 ∷ # 134 ∷ # 72 ∷ # 206 ∷ # 61 ∷ # 2 ∷ [ # 1 ]

EC : OIDValue ECLit
EC = fstₚ (Success.value (toWitness{Q = Logging.val (runParser (parseOIDValue (length ECLit)) ECLit)} tt))

Supported : List (Exists─ _ OIDValue)
Supported = (-, RSA) ∷ [ -, EC ]
