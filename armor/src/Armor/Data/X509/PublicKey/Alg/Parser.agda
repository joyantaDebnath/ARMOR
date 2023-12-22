open import Armor.Prelude

open import Armor.Binary
open import Armor.Data.X509.PublicKey.Alg.ECPKParameters
open import Armor.Data.X509.PublicKey.Alg.TCB
import      Armor.Data.X509.PublicKey.Alg.TCB.OIDs as OIDs
open import Armor.Data.X690-DER.Null
open import Armor.Data.X690-DER.OID
open import Armor.Data.X690-DER.OctetString
open import Armor.Data.X690-DER.Sequence.DefinedByOID
open import Armor.Data.X690-DER.TLV
import      Armor.Grammar.Definitions
import      Armor.Grammar.Parallel
import      Armor.Grammar.Parser
import      Armor.Grammar.Properties

module Armor.Data.X509.PublicKey.Alg.Parser where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Parallel    UInt8
open Armor.Grammar.Parser      UInt8
-- open Armor.Grammar.Properties  UInt8
-- open Armor.Grammar.Sum         UInt8

private
  here' = "X509: PublicKey: Alg"

parseParams : ∀ n {@0 bs} → (o : OID bs) (o∈? : Dec ((-, TLV.val o) ∈ OIDs.Supported))
              → Parser (Logging ∘ Dec) (ExactLength (PKParameters' o o∈?) n)
parseParams n o (no ¬p) =
  OctetString.parseValue n
parseParams n o (yes (here px)) =
  parseExactLength TLV.nosubstrings (tell $ here' String.++ " (params): length mismatch (null)") Null.parse n
parseParams n o (yes (there (here px))) =
  parseExactLength ECPKParameters.nosubstrings (tell $ here' String.++ " (params): length mismatch (EC)")
    ECPKParameters.parse n

parse : Parser (Logging ∘ Dec) PublicKeyAlg
parse = DefinedByOID.parse here' λ n o → parseParams n o ((-, TLV.val o) ∈? OIDs.Supported)
