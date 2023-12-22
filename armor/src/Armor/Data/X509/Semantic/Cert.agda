open import Armor.Binary
open import Armor.Data.X509
import      Armor.Data.X509.Extension.TCB.OIDs as OIDs
open import Armor.Data.X509.Semantic.Cert.Utils
import      Armor.Data.X509.Semantic.Cert.R1 as R1
import      Armor.Data.X509.Semantic.Cert.R2 as R2
import      Armor.Data.X509.Semantic.Cert.R3 as R3
import      Armor.Data.X509.Semantic.Cert.R4 as R4
import      Armor.Data.X509.Semantic.Cert.R5 as R5
import      Armor.Data.X509.Semantic.Cert.R6 as R6
import      Armor.Data.X509.Semantic.Cert.R7 as R7
import      Armor.Data.X509.Semantic.Cert.R8 as R8
import      Armor.Data.X509.Semantic.Cert.R9 as R9
import      Armor.Data.X509.Semantic.Cert.R10 as R10
import      Armor.Data.X509.Semantic.Cert.R11 as R11
import      Armor.Data.X509.Semantic.Cert.R12 as R12
import      Armor.Data.X509.Semantic.Cert.R13 as R13
import      Armor.Data.X509.Semantic.Cert.R14 as R14
import      Armor.Data.X509.Semantic.Cert.R15 as R15
import      Armor.Data.X509.Semantic.Cert.R16 as R16
import      Armor.Data.X509.Semantic.Cert.R17 as R17
import      Armor.Data.X509.Semantic.Cert.R18 as R18
import      Armor.Grammar.Definitions
import      Armor.Grammar.Option
open import Armor.Grammar.IList as IList
open import Armor.Prelude

module Armor.Data.X509.Semantic.Cert where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Option      UInt8

---------------------- SCP rules -----------------

-- SignatureAlgorithm field MUST contain the same algorithm identifier as
-- the Signature field in the sequence TbsCertificate.
open R1 public

-- Extension field MUST only appear if the Version is 3(2).
open R2 public

-- The Serial number MUST be a positive integer assigned by the CA to each certificate.
open R3 public

-- The Issuer field MUST contain a non-empty distinguished name (DN).
-- TODO : fix the parser to enforce set length to minimum 1
open R4 public


-- If the Subject is a CA (e.g., the Basic Constraints extension, is present and the value of CA is TRUE),
-- then the Subject field MUST be populated with a non-empty distinguished name.
open R5 public

-- -- Unique Identifiers fields MUST only appear if the Version is 2 or 3.
open R6 public


-- -- Where it appears, the PathLenConstraint field MUST be greater than or equal to zero.
open R7 public

-- if the Subject is a CRL issuer (e.g., the Key Usage extension, is present and the value of CRLSign is TRUE),
-- then the Subject field MUST be populated with a non-empty distinguished name.
open R8 public

-- When the Key Usage extension appears in a certificate, at least one of the bits MUST be set to 1.
open R9 public

-- If subject naming information is present only in the Subject Alternative Name extension ,
-- then the Subject name MUST be an empty sequence and the Subject Alternative Name extension MUST be critical.
-- If the subject field contains an empty sequence, then the issuing CA MUST include a
-- subjectAltName extension that is marked as critical.
open R10 public

-- If the Subject Alternative Name extension is present, the sequence MUST contain at least one entry.
open R11 public

-- If the KeyCertSign bit is asserted, then the CA bit in the Basic Constraints extension MUST also be asserted.
open R12 public

-- A certificate MUST NOT include more than one instance of a particular Extension.
open R13 public

-- A certificate-using system MUST reject the certificate if it encounters a critical Extension
-- it does not recognize or a critical Extension that contains information that it cannot process.
open R14 public

-- A certificate policy OID MUST NOT appear more than once in a Certificate Policies extension.
open R15 public

-- While each of these fields is optional, a DistributionPoint MUST NOT consist of only the Reasons field;
-- either distributionPoint or CRLIssuer MUST be present.
open R16 public

-- The certificate Validity period includes the current time
open R17 public

--- consistency of certificate purposes based on key usage bits and extended key usage OIDs
open R18 public
