open import Armor.Binary
import      Armor.Data.X509.Extension.AIA.AccessDesc.TCB.OIDs as OIDs
open import Armor.Data.X509.Extension.AIA.AccessDesc.TCB
open import Armor.Data.X509.GeneralNames.GeneralName
open import Armor.Data.X690-DER.OID
open import Armor.Data.X690-DER.Sequence.DefinedByOID
open import Armor.Data.X690-DER.TLV
import      Armor.Grammar.Definitions
import      Armor.Grammar.Parallel
import      Armor.Grammar.Parser
open import Armor.Prelude

module Armor.Data.X509.Extension.AIA.AccessDesc.Parser where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Parallel    UInt8
open Armor.Grammar.Parser      UInt8

private
  here' = "X509: Extension: AIA: AccessDesc:"


parseAccessDesc : Parser (Logging ∘ Dec) AccessDesc
parseAccessDesc =
  DefinedByOID.parse here'
    λ n o →
      parseExactLength (Parallel.nosubstrings₁ GeneralName.nosubstrings)
        (tell $ here' String.++ ": length mismatch")
        (parse×Dec GeneralName.nosubstrings
          (tell $ here' String.++ ": unknonwn OID")
          parseGeneralName
          λ x → T-dec)
        n
