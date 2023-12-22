open import Armor.Binary
open import Armor.Data.X509
import      Armor.Data.X509.Extension.TCB.OIDs as OIDs
open import Armor.Data.X509.Semantic.Cert.Utils
import      Armor.Grammar.Definitions
import      Armor.Grammar.Option
open import Armor.Grammar.IList as IList
open import Armor.Prelude

module Armor.Data.X509.Semantic.Cert.R16 where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Option      UInt8

--- https://datatracker.ietf.org/doc/html/rfc5280#section-4.2.1.13
-- While each of these fields is optional, a DistributionPoint MUST NOT consist of only the Reasons field;
-- either distributionPoint or CRLIssuer MUST be present.

R16 : ∀ {@0 bs} → Cert bs → Set
R16 c = T (checkCRLDistStruct (Cert.getCRLDIST c))

r16 : ∀ {@0 bs} (c : Cert bs) → Dec (R16 c)
r16 c = T-dec

