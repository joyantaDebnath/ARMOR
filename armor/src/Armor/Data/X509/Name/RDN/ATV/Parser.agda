open import Armor.Binary
open import Armor.Data.X509.DirectoryString
open import Armor.Data.X509.Name.RDN.ATV.OIDs
open import Armor.Data.X509.Name.RDN.ATV.TCB
open import Armor.Data.X690-DER.OID
open import Armor.Data.X690-DER.Sequence.DefinedByOID
open import Armor.Data.X690-DER.Strings.IA5String
open import Armor.Data.X690-DER.Strings.PrintableString
open import Armor.Data.X690-DER.TLV
import      Armor.Grammar.Definitions
import      Armor.Grammar.Parallel
import      Armor.Grammar.Parser
open import Armor.Prelude

module Armor.Data.X509.Name.RDN.ATV.Parser where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Parser      UInt8
open Armor.Grammar.Parallel    UInt8

private
  here' = "X509: Name: RDNSequence: RDN: ATV"

parse : Parser (Logging ∘ Dec) ATV
parse = DefinedByOID.parse here' λ n o → p n o ((-, TLV.val o) ∈? Supported)
  where
  p : ∀ n {@0 bs} → (o : OID bs) → (d : Dec ((-, TLV.val o) ∈ Supported)) → Parser (Logging ∘ Dec) (ExactLength (ATVParam o d) n)
  runParser (p n o (no ¬p)) xs = do
    tell $ here' String.++ ": defaulting to directory string"
    runParser
      (parseExactLength DirectoryString.nosubstrings (tell $ here' String.++ ": length mismatch")
        parseDirectoryString n)
      xs
  runParser (p n o (yes (here px)))  xs = do
    tell $ here' String.++ ": X520DNQUALIFIER"
    runParser
      (parseExactLength TLV.nosubstrings (tell $ here' String.++ ": length mismatch")
        parsePrintableString n)
      xs
  runParser (p n o (yes (there (here px)))) xs = do
    tell $ here' String.++ ": X520COUNTRYNAME"
    runParser
      (parseExactLength (Parallel.nosubstrings₁ TLV.nosubstrings) (tell $ here' String.++ ": length mismatch")
        (parseTLVSizeBound _ PrintableString.sizeUnique 2 2 (here' String.++ ": X520COUNTRYNAME") parsePrintableString) n)
      xs
  runParser (p n o (yes (there (there (here px))))) xs = do
    tell $ here' String.++ ": X520SERIALNUMBER"
    runParser
      (parseExactLength TLV.nosubstrings (tell $ here' String.++ ": length mismatch")
        parsePrintableString n)
      xs
  runParser (p n o (yes (there (there (there (here px)))))) xs = do
    tell $ here' String.++ ": PCKS9-ID-EMAILADDRESS"
    runParser
      (parseExactLength TLV.nosubstrings (tell $ here' String.++ ": length mismatch")
        parseIA5String n)
      xs

  runParser (p n o (yes (there (there (there (there (here px))))))) xs = do
    tell $ here' String.++ ": DomainComponent"
    runParser
      (parseExactLength TLV.nosubstrings (tell $ here' String.++ ": length mismatch")
        parseIA5String n)
      xs
