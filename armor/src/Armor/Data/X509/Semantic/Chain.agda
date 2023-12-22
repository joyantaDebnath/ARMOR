{-# OPTIONS --sized-types #-}

import      Armor.Binary
open import Armor.Data.X509
open import Armor.Data.X509.Semantic.StringPrep.ExecDS
open import Armor.Data.X509.Semantic.StringPrep.ExecPS
open import Armor.Data.X509.Semantic.StringPrep.ExecIS
open import Armor.Data.X509.Semantic.Cert
open import Armor.Data.X509.Semantic.Cert.Utils
import      Armor.Data.X509.Semantic.Chain.Builder as Chain
open import Armor.Data.X509.Semantic.Chain.NameMatch
import      Armor.Data.X509.Semantic.Chain.R19     as R19
import      Armor.Data.X509.Semantic.Chain.R20     as R20
import      Armor.Data.X509.Semantic.Chain.R21     as R21
import      Armor.Data.X509.Semantic.Chain.R22     as R22
import      Armor.Data.X509.Semantic.Chain.R23     as R23
open import Armor.Data.X509.Semantic.Chain.TCB     as Chain
import      Armor.Grammar.Definitions
open import Armor.Grammar.IList as IList
import      Armor.Grammar.Option
import      Armor.Grammar.Parallel
open import Armor.Prelude

open import  Armor.Data.X509.Name.RDN.ATV.OIDs

module Armor.Data.X509.Semantic.Chain where

open Armor.Binary
open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Option      UInt8
open Armor.Grammar.Parallel    UInt8


-- https://datatracker.ietf.org/doc/html/rfc5280#section-6.1.4 (k)
-- Conforming implementations may choose to reject all Version 1 and Version 2 intermediate CA certificates
open R19 public

-- https://datatracker.ietf.org/doc/html/rfc5280#section-4.2.1.9
-- The PathLenConstraint field is meaningful only if the CA boolean
-- is asserted and the Key Usage extension, if present, asserts the KeyCertSign bit. In this case, it gives
-- the maximum number of non-self-issued intermediate certificates that may follow this certificate in a valid certification path.

open R20 public

-- https://datatracker.ietf.org/doc/html/rfc5280#section-4.2.1.13
-- For DistributionPoint field, if the certificate issuer is not the CRL issuer,
-- then the CRLIssuer field MUST be present and contain the Name of the CRL issuer. If the
-- certificate issuer is also the CRL issuer, then conforming CAs MUST omit the CRLIssuer
-- field and MUST include the distributionPoint field.
open R21 public

-- https://datatracker.ietf.org/doc/html/rfc5280#section-6.1
-- A certificate MUST NOT appear more than once in a prospective certification path.

open R22 public

-- https://datatracker.ietf.org/doc/html/rfc5280#section-6.1.4
--- Every non-leaf certificate in a chain must be a CA certificate

open R23 public

-- R24 and R25 are enforced by the chain builder
-- R26 and R27 are enforced by the unverified Python driver
