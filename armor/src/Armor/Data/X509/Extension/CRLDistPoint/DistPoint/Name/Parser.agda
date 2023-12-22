open import Armor.Binary
open import Armor.Data.X509.Extension.CRLDistPoint.DistPoint.Name.Properties
open import Armor.Data.X509.Extension.CRLDistPoint.DistPoint.Name.TCB
open import Armor.Data.X509.GeneralNames
open import Armor.Data.X509.Name
open import Armor.Data.X690-DER.SequenceOf
open import Armor.Data.X690-DER.TLV
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Definitions
import      Armor.Grammar.Parser
import      Armor.Grammar.Sum
open import Armor.Prelude

module Armor.Data.X509.Extension.CRLDistPoint.DistPoint.Name.Parser where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Parser      UInt8
open Armor.Grammar.Sum         UInt8

private
  here' = "X509: Extension: CRLDistPoint: DistPoint: Name"

parseFullName = parseTLV Tag.AA0 (here' String.++ ": full name") _ parseGeneralNamesElems

parseNameRTCrlIssuer : Parser (Logging ∘ Dec) NameRTCrlIssuer
parseNameRTCrlIssuer = Name.RDN.[ Tag.AA1 ]parse

parseDistPointNameChoice : Parser (Logging ∘ Dec) DistPointNameChoice
parseDistPointNameChoice =
  parseEquivalent equivalentDistPointNameChoice
    (parseSum parseFullName parseNameRTCrlIssuer)
