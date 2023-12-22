open import Armor.Binary
open import Armor.Data.X690-DER.OID.Parser
open import Armor.Data.X690-DER.OID.TCB
import      Armor.Grammar.Parallel.TCB
import      Armor.Grammar.Parser
open import Armor.Prelude

module Armor.Data.X509.SignAlg.TCB.OIDs where

open Armor.Grammar.Parallel.TCB UInt8
open Armor.Grammar.Parser       UInt8

module RSA where

{-
https://datatracker.ietf.org/doc/html/rfc3279#section-2.2

The signature algorithm with MD2 and the RSA encryption algorithm is
defined in PKCS #1 [RFC 2313].  As defined in PKCS #1 [RFC 2313], the
ASN.1 OID used to identify this signature algorithm is:

   md2WithRSAEncryption OBJECT IDENTIFIER  ::=  {
       iso(1) member-body(2) us(840) rsadsi(113549) pkcs(1)
       pkcs-1(1) 2  }

The signature algorithm with MD5 and the RSA encryption algorithm is
defined in PKCS #1 [RFC 2313].  As defined in PKCS #1 [RFC 2313], the
ASN.1 OID used to identify this signature algorithm is:

    md5WithRSAEncryption OBJECT IDENTIFIER  ::=  {
        iso(1) member-body(2) us(840) rsadsi(113549) pkcs(1)
        pkcs-1(1) 4  }

The ASN.1 object identifier used to identify this signature algorithm
is:

      sha-1WithRSAEncryption OBJECT IDENTIFIER  ::=  {
          iso(1) member-body(2) us(840) rsadsi(113549) pkcs(1)
          pkcs-1(1) 5  }

When any of these three OIDs appears within the ASN.1 type
AlgorithmIdentifier, the parameters component of that type SHALL be
the ASN.1 type NULL.
-}

  MD2Lit : List UInt8
  MD2Lit = # 42 ∷ # 134 ∷ # 72 ∷ # 134 ∷ # 247 ∷ # 13 ∷ # 1 ∷ # 1 ∷ [ # 2 ]

  MD2 : OIDValue MD2Lit
  MD2 = fstₚ (Success.value (toWitness{Q = Logging.val (runParser (parseOIDValue (length MD2Lit)) MD2Lit)} tt))

  MD5Lit : List UInt8
  MD5Lit = # 42 ∷ # 134 ∷ # 72 ∷ # 134 ∷ # 247 ∷ # 13 ∷ # 1 ∷ # 1 ∷ [ # 4 ]

  MD5 : OIDValue MD5Lit
  MD5 = fstₚ (Success.value (toWitness{Q = Logging.val (runParser (parseOIDValue (length MD5Lit)) MD5Lit)} tt))

  SHA1Lit : List UInt8
  SHA1Lit = # 42 ∷ # 134 ∷ # 72 ∷ # 134 ∷ # 247 ∷ # 13 ∷ # 1 ∷ # 1 ∷ [ # 5 ]

  SHA1 : OIDValue SHA1Lit
  SHA1 = fstₚ (Success.value (toWitness{Q = Logging.val (runParser (parseOIDValue (length SHA1Lit)) SHA1Lit)} tt))

{-
https://datatracker.ietf.org/doc/html/rfc4055#section-5

The object identifier used to identify the PKCS #1 version 1.5
   signature algorithm with SHA-224 is:

      sha224WithRSAEncryption  OBJECT IDENTIFIER  ::=  { pkcs-1 14 }

   The object identifier used to identify the PKCS #1 version 1.5
   signature algorithm with SHA-256 is:

      sha256WithRSAEncryption  OBJECT IDENTIFIER  ::=  { pkcs-1 11 }

   The object identifier used to identify the PKCS #1 version 1.5
   signature algorithm with SHA-384 is:

      sha384WithRSAEncryption  OBJECT IDENTIFIER  ::=  { pkcs-1 12 }

   The object identifier used to identify the PKCS #1 version 1.5
   signature algorithm with SHA-512 is:

      sha512WithRSAEncryption  OBJECT IDENTIFIER  ::=  { pkcs-1 13 }

   When any of these four object identifiers appears within an
   AlgorithmIdentifier, the parameters MUST be NULL.  Implementations
   MUST accept the parameters being absent as well as present.

-}

  SHA224Lit : List UInt8
  SHA224Lit = # 42 ∷ # 134 ∷ # 72 ∷ # 134 ∷ # 247 ∷ # 13 ∷ # 1 ∷ # 1 ∷ [ # 14 ]

  SHA224 : OIDValue SHA224Lit
  SHA224 = fstₚ (Success.value (toWitness{Q = Logging.val (runParser (parseOIDValue (length SHA224Lit)) SHA224Lit)} tt))

  SHA256Lit : List UInt8
  SHA256Lit = # 42 ∷ # 134 ∷ # 72 ∷ # 134 ∷ # 247 ∷ # 13 ∷ # 1 ∷ # 1 ∷ [ # 11 ]

  SHA256 : OIDValue SHA256Lit
  SHA256 = fstₚ (Success.value (toWitness{Q = Logging.val (runParser (parseOIDValue (length SHA256Lit)) SHA256Lit)} tt))

  SHA384Lit : List UInt8
  SHA384Lit = # 42 ∷ # 134 ∷ # 72 ∷ # 134 ∷ # 247 ∷ # 13 ∷ # 1 ∷ # 1 ∷ [ # 12 ]

  SHA384 : OIDValue SHA384Lit
  SHA384 = fstₚ (Success.value (toWitness{Q = Logging.val (runParser (parseOIDValue (length SHA384Lit)) SHA384Lit)} tt))

  SHA512Lit : List UInt8
  SHA512Lit = # 42 ∷ # 134 ∷ # 72 ∷ # 134 ∷ # 247 ∷ # 13 ∷ # 1 ∷ # 1 ∷ [ # 13 ]

  SHA512 : OIDValue SHA512Lit
  SHA512 = fstₚ (Success.value (toWitness{Q = Logging.val (runParser (parseOIDValue (length SHA512Lit)) SHA512Lit)} tt))

{-
https://datatracker.ietf.org/doc/html/rfc4055#section-3.1

When RSASSA-PSS is used in an AlgorithmIdentifier, the parameters
MUST employ the RSASSA-PSS-params syntax.  The parameters may be
either absent or present when used as subject public key information.
The parameters MUST be present when used in the algorithm identifier
associated with a signature value.

When signing, it is RECOMMENDED that the parameters, except for
possibly saltLength, remain fixed for all usages of a given RSA key
pair.

  id-RSASSA-PSS  OBJECT IDENTIFIER  ::=  { pkcs-1 10 }
-}

  PSSLit : List UInt8
  PSSLit = # 42 ∷ # 134 ∷ # 72 ∷ # 134 ∷ # 247 ∷ # 13 ∷ # 1 ∷ # 1 ∷ [ # 10 ]

  PSS : OIDValue PSSLit
  PSS = fstₚ (Success.value (toWitness{Q = Logging.val (runParser (parseOIDValue (length PSSLit)) PSSLit)} tt))

  ExplicitNullParam : List (Exists─ _ OIDValue)
  ExplicitNullParam = (-, MD2) ∷ (-, MD5) ∷ (-, SHA1) ∷ []

  ExplicitOrImplicitNullParam : List (Exists─ _ OIDValue)
  ExplicitOrImplicitNullParam = (-, SHA224) ∷ (-, SHA256 ) ∷ (-, SHA384) ∷ (-, SHA512) ∷ []

  Supported : List (Exists─ _ OIDValue)
  Supported = ExplicitNullParam ++ ExplicitOrImplicitNullParam ++ [ -, PSS ]

module DSA where

{-
https://datatracker.ietf.org/doc/html/rfc3279#section-2.2.2

The ASN.1 OID used to identify
   this signature algorithm is:

      id-dsa-with-sha1 OBJECT IDENTIFIER ::=  {
           iso(1) member-body(2) us(840) x9-57 (10040)
           x9cm(4) 3 }

   When the id-dsa-with-sha1 algorithm identifier appears as the
   algorithm field in an AlgorithmIdentifier, the encoding SHALL omit
   the parameters field.  That is, the AlgorithmIdentifier SHALL be a
   SEQUENCE of one component: the OBJECT IDENTIFIER id-dsa-with-sha1.
-}

  SHA1Lit : List UInt8
  SHA1Lit = # 42 ∷ # 134 ∷ # 72 ∷ # 206 ∷ # 56 ∷ # 4 ∷ [ # 3 ]

  SHA1 : OIDValue SHA1Lit
  SHA1 = fstₚ (Success.value (toWitness{Q = Logging.val (runParser (parseOIDValue (length SHA1Lit)) SHA1Lit)} tt))

{-
https://www.ietf.org/rfc/rfc5758.txt

When SHA-224 is used, the OID is:

   id-dsa-with-sha224 OBJECT IDENTIFIER  ::=  { joint-iso-ccitt(2)
       country(16) us(840) organization(1) gov(101) csor(3)
       algorithms(4) id-dsa-with-sha2(3) 1 }.

When SHA-256 is used, the OID is:

   id-dsa-with-sha256 OBJECT IDENTIFIER  ::=  { joint-iso-ccitt(2)
       country(16) us(840) organization(1) gov(101) csor(3)
       algorithms(4) id-dsa-with-sha2(3) 2 }.

When the id-dsa-with-sha224 or id-dsa-with-sha256 algorithm
identifier appears in the algorithm field as an AlgorithmIdentifier,
the encoding SHALL omit the parameters field.  That is, the
AlgorithmIdentifier SHALL be a SEQUENCE of one component, the OID id-
dsa-with-sha224 or id-dsa-with-sha256.
-}

  SHA224Lit : List UInt8
  SHA224Lit = # 96 ∷ # 134 ∷ # 72 ∷ # 1 ∷ # 101 ∷ # 3 ∷ # 4 ∷ # 3 ∷ [ # 1 ]

  SHA224 : OIDValue SHA224Lit
  SHA224 = fstₚ (Success.value (toWitness{Q = Logging.val (runParser (parseOIDValue (length SHA224Lit)) SHA224Lit)} tt))

  SHA256Lit : List UInt8
  SHA256Lit = # 96 ∷ # 134 ∷ # 72 ∷ # 1 ∷ # 101 ∷ # 3 ∷ # 4 ∷ # 3 ∷ [ # 2 ]

  SHA256 : OIDValue SHA256Lit
  SHA256 = fstₚ (Success.value (toWitness{Q = Logging.val (runParser (parseOIDValue (length SHA256Lit)) SHA256Lit)} tt))

  Supported : List (Exists─ _ OIDValue)
  Supported = (-, SHA1) ∷ (-, SHA224) ∷ [ -, SHA256 ]

module ECDSA where

{-
https://datatracker.ietf.org/doc/html/rfc3279#section-2.2.3

The ASN.1 object identifiers used to identify ECDSA are defined in the
following arc:

      ansi-X9-62  OBJECT IDENTIFIER ::= {
           iso(1) member-body(2) us(840) 10045 }

      id-ecSigType OBJECT IDENTIFIER  ::=  {
           ansi-X9-62 signatures(4) }

 ECDSA is used in conjunction with the SHA-1 one-way hash function.
 The ASN.1 object identifier used to identify ECDSA with SHA-1 is:

      ecdsa-with-SHA1  OBJECT IDENTIFIER ::= {
           id-ecSigType 1 }

When the ecdsa-with-SHA1 algorithm identifier appears as the
algorithm field in an AlgorithmIdentifier, the encoding MUST omit the
parameters field.  That is, the AlgorithmIdentifier SHALL be a
SEQUENCE of one component: the OBJECT IDENTIFIER ecdsa-with-SHA1.
-}

  SHA1Lit : List UInt8
  SHA1Lit = # 42 ∷ # 134 ∷ # 72 ∷ # 206 ∷ # 61 ∷ # 4 ∷ [ # 1 ]

  SHA1 : OIDValue SHA1Lit
  SHA1 = fstₚ (Success.value (toWitness{Q = Logging.val (runParser (parseOIDValue (length SHA1Lit)) SHA1Lit)} tt))

{-
The ASN.1 OIDs used to specify that an ECDSA signature was generated
using SHA-224, SHA-256, SHA-384, or SHA-512 are, respectively:

   ecdsa-with-SHA224 OBJECT IDENTIFIER ::= { iso(1) member-body(2)
        us(840) ansi-X9-62(10045) signatures(4) ecdsa-with-SHA2(3) 1 }

   ecdsa-with-SHA256 OBJECT IDENTIFIER ::= { iso(1) member-body(2)
        us(840) ansi-X9-62(10045) signatures(4) ecdsa-with-SHA2(3) 2 }

   ecdsa-with-SHA384 OBJECT IDENTIFIER ::= { iso(1) member-body(2)
        us(840) ansi-X9-62(10045) signatures(4) ecdsa-with-SHA2(3) 3 }

   ecdsa-with-SHA512 OBJECT IDENTIFIER ::= { iso(1) member-body(2)
        us(840) ansi-X9-62(10045) signatures(4) ecdsa-with-SHA2(3) 4 }

When the ecdsa-with-SHA224, ecdsa-with-SHA256, ecdsa-with-SHA384, or
ecdsa-with-SHA512 algorithm identifier appears in the algorithm field
as an AlgorithmIdentifier, the encoding MUST omit the parameters
field.  That is, the AlgorithmIdentifier SHALL be a SEQUENCE of one
component, the OID ecdsa-with-SHA224, ecdsa-with-SHA256, ecdsa-with-
SHA384, or ecdsa-with-SHA512.
-}

  SHA224Lit : List UInt8
  SHA224Lit = # 42 ∷ # 134 ∷ # 72 ∷ # 206 ∷ # 61 ∷ # 4 ∷ # 3 ∷ [ # 1 ]

  SHA224 : OIDValue SHA224Lit
  SHA224 = fstₚ (Success.value (toWitness{Q = Logging.val (runParser (parseOIDValue (length SHA224Lit)) SHA224Lit)} tt))

  SHA256Lit : List UInt8
  SHA256Lit = # 42 ∷ # 134 ∷ # 72 ∷ # 206 ∷ # 61 ∷ # 4 ∷ # 3 ∷ [ # 2 ]

  SHA256 : OIDValue SHA256Lit
  SHA256 = fstₚ (Success.value (toWitness{Q = Logging.val (runParser (parseOIDValue (length SHA256Lit)) SHA256Lit)} tt))

  SHA384Lit : List UInt8
  SHA384Lit = # 42 ∷ # 134 ∷ # 72 ∷ # 206 ∷ # 61 ∷ # 4 ∷ # 3 ∷ [ # 3 ]

  SHA384 : OIDValue SHA384Lit
  SHA384 = fstₚ (Success.value (toWitness{Q = Logging.val (runParser (parseOIDValue (length SHA384Lit)) SHA384Lit)} tt))

  SHA512Lit : List UInt8
  SHA512Lit = # 42 ∷ # 134 ∷ # 72 ∷ # 206 ∷ # 61 ∷ # 4 ∷ # 3 ∷ [ # 4 ]

  SHA512 : OIDValue SHA512Lit
  SHA512 = fstₚ (Success.value (toWitness{Q = Logging.val (runParser (parseOIDValue (length SHA512Lit)) SHA512Lit)} tt))

  Supported : List (Exists─ _ OIDValue)
  Supported = (-, SHA1) ∷ (-, SHA224) ∷ (-, SHA256) ∷ (-, SHA384) ∷ [ -, SHA512 ]

Supported : List (Exists─ _ OIDValue)
Supported = DSA.Supported ++ ECDSA.Supported ++ RSA.Supported
