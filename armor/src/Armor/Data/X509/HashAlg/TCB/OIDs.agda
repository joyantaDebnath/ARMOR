open import Armor.Binary
open import Armor.Data.X690-DER.OID.Parser
open import Armor.Data.X690-DER.OID.TCB
import      Armor.Grammar.Parallel.TCB
import      Armor.Grammar.Parser
open import Armor.Prelude

module Armor.Data.X509.HashAlg.TCB.OIDs where

open Armor.Grammar.Parallel.TCB UInt8
open Armor.Grammar.Parser       UInt8

{-
-- https://datatracker.ietf.org/doc/html/rfc4055#section-2.1
-- 
-- These one-way hash functions are identified by the following object
-- identifiers:
--
--    id-sha1  OBJECT IDENTIFIER  ::=  { iso(1)
--                         identified-organization(3) oiw(14)
--                         secsig(3) algorithms(2) 26 }
--    id-sha224  OBJECT IDENTIFIER  ::=  {{ joint-iso-itu-t(2)
--                         country(16) us(840) organization(1) gov(101)
--                         csor(3) nistalgorithm(4) hashalgs(2) 4 }
--    id-sha256  OBJECT IDENTIFIER  ::=  { joint-iso-itu-t(2)
--                         country(16) us(840) organization(1) gov(101)
--                         csor(3) nistalgorithm(4) hashalgs(2) 1 }
--    id-sha384  OBJECT IDENTIFIER  ::=  { joint-iso-itu-t(2)
--                         country(16) us(840) organization(1) gov(101)
--                         csor(3) nistalgorithm(4) hashalgs(2) 2 }
--    id-sha512  OBJECT IDENTIFIER  ::=  { joint-iso-itu-t(2)
--                         country(16) us(840) organization(1) gov(101)
--                         csor(3) nistalgorithm(4) hashalgs(2) 3 }
-- 
-- There are two possible encodings for the AlgorithmIdentifier
-- parameters field associated with these object identifiers.  The two
-- alternatives arise from the loss of the OPTIONAL associated with the
-- algorithm identifier parameters when the 1988 syntax for
-- AlgorithmIdentifier was translated into the 1997 syntax.  Later the
-- OPTIONAL was recovered via a defect report, but by then many people
-- thought that algorithm parameters were mandatory.  Because of this
-- history some implementations encode parameters as a NULL element
-- while others omit them entirely.  The correct encoding is to omit the
-- parameters field; however, when RSASSA-PSS and RSAES-OAEP were
-- defined, it was done using the NULL parameters rather than absent
-- parameters.
--
-- All implementations MUST accept both NULL and absent parameters as
-- legal and equivalent encodings.
--
-- To be clear, the following algorithm identifiers are used when a NULL
-- parameter MUST be present:
--
--    sha1Identifier  AlgorithmIdentifier  ::=  { id-sha1, NULL }
--    sha224Identifier  AlgorithmIdentifier  ::=  { id-sha224, NULL }
--    sha256Identifier  AlgorithmIdentifier  ::=  { id-sha256, NULL }
--    sha384Identifier  AlgorithmIdentifier  ::=  { id-sha384, NULL }
--    sha512Identifier  AlgorithmIdentifier  ::=  { id-sha512, NULL }
-}

SHA1Lit SHA224Lit SHA256Lit SHA384Lit SHA512Lit : List UInt8

SHA1Lit = # 43 ∷ # 14 ∷ # 3 ∷ # 2 ∷ [ # 26 ]

SHA1 : OIDValue SHA1Lit
SHA1 = fstₚ (Success.value (toWitness{Q = Logging.val (runParser (parseOIDValue (length SHA1Lit)) SHA1Lit)} tt))

SHA224Lit = # 96 ∷ # 134 ∷ # 72 ∷ # 1 ∷ # 101 ∷ # 3 ∷ # 4 ∷ # 2 ∷ [ # 4 ] 

SHA224 : OIDValue SHA224Lit
SHA224 = fstₚ (Success.value (toWitness{Q = Logging.val (runParser (parseOIDValue (length SHA224Lit)) SHA224Lit)} tt))

SHA256Lit = # 96 ∷ # 134 ∷ # 72 ∷ # 1 ∷ # 101 ∷ # 3 ∷ # 4 ∷ # 2 ∷ [ # 1 ] 

SHA256 : OIDValue SHA256Lit
SHA256 = fstₚ (Success.value (toWitness{Q = Logging.val (runParser (parseOIDValue (length SHA256Lit)) SHA256Lit)} tt))

SHA384Lit = # 96 ∷ # 134 ∷ # 72 ∷ # 1 ∷ # 101 ∷ # 3 ∷ # 4 ∷ # 2 ∷ [ # 2 ]

SHA384 : OIDValue SHA384Lit
SHA384 = fstₚ (Success.value (toWitness{Q = Logging.val (runParser (parseOIDValue (length SHA384Lit)) SHA384Lit)} tt))

SHA512Lit = # 96 ∷ # 134 ∷ # 72 ∷ # 1 ∷ # 101 ∷ # 3 ∷ # 4 ∷ # 2 ∷ [ # 3 ]

SHA512 : OIDValue SHA512Lit
SHA512 = fstₚ (Success.value (toWitness{Q = Logging.val (runParser (parseOIDValue (length SHA512Lit)) SHA512Lit)} tt))

RFC4055 : List (Exists─ _ OIDValue)
RFC4055 = (-, SHA1) ∷ (-, SHA224) ∷ (-, SHA256) ∷ (-, SHA384) ∷ (-, SHA512) ∷ []
