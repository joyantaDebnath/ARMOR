open import Armor.Binary
open import Armor.Data.X690-DER.OID
import      Armor.Grammar.Definitions
import      Armor.Grammar.Parallel.TCB
import      Armor.Grammar.Parser
open import Armor.Prelude

module Armor.Data.X509.Name.RDN.ATV.OIDs where

open Armor.Grammar.Definitions  UInt8
open Armor.Grammar.Parallel.TCB UInt8
open Armor.Grammar.Parser       UInt8

-- https://datatracker.ietf.org/doc/html/rfc5280#appendix-A.1
--
-- suggested naming attributes: Definition of the following
--   information object set may be augmented to meet local
--   requirements.  Note that deleting members of the set may
--   prevent interoperability with conforming implementations.
-- presented in pairs: the AttributeType followed by the
--   type definition for the corresponding AttributeValue

{-
-- Arc for standard naming attributes
-- 
-- id-at OBJECT IDENTIFIER ::= { joint-iso-ccitt(2) ds(5) 4 }
-}

ID-AT-Lit : List UInt8
ID-AT-Lit = # 85 ∷ [ # 4 ]

{- 
-- -- Naming attributes of type X520dnQualifier
-- 
-- id-at-dnQualifier       AttributeType ::= { id-at 46 }
-- 
-- X520dnQualifier ::=     PrintableString
-}

X520DNQUALIFIER-Lit : List UInt8
X520DNQUALIFIER-Lit = ID-AT-Lit ++ [ # 46 ]

X520DNQUALIFIER : OIDValue X520DNQUALIFIER-Lit
X520DNQUALIFIER =
  fstₚ (Success.value (toWitness{Q = Logging.val (runParser (parseOIDValue (length X520DNQUALIFIER-Lit)) X520DNQUALIFIER-Lit)} tt))

{-
-- -- Naming attributes of type X520countryName (digraph from IS 3166)
-- 
-- id-at-countryName       AttributeType ::= { id-at 6 }
-- 
-- X520countryName ::=     PrintableString (SIZE (2))
-}

X520COUNTRYNAME-Lit : List UInt8
X520COUNTRYNAME-Lit = ID-AT-Lit ++ [ # 6 ]

X520COUNTRYNAME : OIDValue X520COUNTRYNAME-Lit
X520COUNTRYNAME =
  fstₚ (Success.value (toWitness{Q = Logging.val (runParser (parseOIDValue (length X520COUNTRYNAME-Lit)) X520COUNTRYNAME-Lit)} tt))

{-
-- -- Naming attributes of type X520SerialNumber
-- 
-- id-at-serialNumber      AttributeType ::= { id-at 5 }
-- 
-- X520SerialNumber ::=    PrintableString (SIZE (1..ub-serial-number))
-}

X520SERIALNUMBER-Lit : List UInt8
X520SERIALNUMBER-Lit = ID-AT-Lit ++ [ # 5 ]

X520SERIALNUMBER : OIDValue X520SERIALNUMBER-Lit
X520SERIALNUMBER =
  fstₚ (Success.value (toWitness{Q = Logging.val (runParser (parseOIDValue (length X520SERIALNUMBER-Lit)) X520SERIALNUMBER-Lit)} tt))

{-
-- -- Legacy attributes
--
-- pkcs-9 OBJECT IDENTIFIER ::=
--        { iso(1) member-body(2) us(840) rsadsi(113549) pkcs(1) 9 }
--
-- id-emailAddress      AttributeType ::= { pkcs-9 1 }
--
-- EmailAddress ::=     IA5String (SIZE (1..ub-emailaddress-length))
-}

PCKS9-ID-EMAILADDRESS-Lit : List UInt8
PCKS9-ID-EMAILADDRESS-Lit = # 42 ∷ # 134 ∷ # 72 ∷ # 134 ∷ # 247 ∷ # 13 ∷ # 1 ∷ # 9 ∷ [ # 1 ]

PCKS9-ID-EMAILADDRESS : OIDValue PCKS9-ID-EMAILADDRESS-Lit
PCKS9-ID-EMAILADDRESS =
  fstₚ (Success.value (toWitness{Q = Logging.val (runParser (parseOIDValue (length PCKS9-ID-EMAILADDRESS-Lit)) PCKS9-ID-EMAILADDRESS-Lit)} tt))

{-
-- Naming attributes of type DomainComponent (from RFC 4519)

-- id-domainComponent   AttributeType ::= { 0 9 2342 19200300 100 1 25 }

-- DomainComponent ::=  IA5String
-}

DomainComponent-Lit : List UInt8
DomainComponent-Lit = # 9 ∷ # 146 ∷ # 38 ∷ # 137 ∷ # 147 ∷ # 242 ∷ # 44 ∷ # 100 ∷ # 1 ∷ [ # 25 ]

DomainComponent : OIDValue DomainComponent-Lit
DomainComponent =
  fstₚ (Success.value (toWitness{Q = Logging.val (runParser (parseOIDValue (length DomainComponent-Lit)) DomainComponent-Lit)} tt))

-- For now, we assume anything not in the list of "supported" OIDs for ATV has a
-- AttributeValue type of DirectoryString

Supported : List (Exists─ _ OIDValue)
Supported = (-, X520DNQUALIFIER) ∷ (-, X520COUNTRYNAME) ∷ (-, X520SERIALNUMBER) ∷ (-, PCKS9-ID-EMAILADDRESS) ∷ [ -, DomainComponent ]
