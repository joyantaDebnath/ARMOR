open import Armor.Binary
open import Armor.Data.X509.SignAlg.DSA.TCB
import      Armor.Data.X509.SignAlg.TCB.OIDs as OIDs
open import Armor.Data.X690-DER.OID
open import Armor.Data.X690-DER.Sequence.DefinedByOID
open import Armor.Data.X690-DER.TLV
import      Armor.Grammar.Definitions
import      Armor.Grammar.Parallel
import      Armor.Grammar.Parser
open import Armor.Prelude

module Armor.Data.X509.SignAlg.DSA.Parser where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Parallel    UInt8
open Armor.Grammar.Parser      UInt8

private
  here' = "X509: SignAlg: DSA"

parseParams : ∀ n {@0 bs} → (o : OID bs) (o∈? : Dec ((-, TLV.val o) ∈ OIDs.DSA.Supported))
              → Parser (Logging ∘ Dec) (ExactLength (DSAParams' o o∈?) n)
parseParams n o (no ¬p) =
  parseExactLength (λ where _ ()) silent parseFalse n
parseParams n o (yes p) =
  parseExactLength (λ where _ (─ refl) (─ refl) → refl)
    (tell $ here' String.++ ": parameter should be absent")
    (parseErased (parseLit silent silent [])) n

parse : Parser (Logging ∘ Dec) DSA
parse = DefinedByOID.parse here' λ n o → parseParams n o ((-, TLV.val o) ∈? OIDs.DSA.Supported)
