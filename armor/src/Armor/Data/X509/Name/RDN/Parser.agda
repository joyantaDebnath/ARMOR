open import Armor.Binary
open import Armor.Data.X690-DER.SetOf
open import Armor.Data.X690-DER.SequenceOf
open import Armor.Data.X690-DER.TLV
import      Armor.Data.X690-DER.Tag as Tag
open import Armor.Data.X509.Name.RDN.ATV
open import Armor.Data.X509.Name.RDN.Properties
open import Armor.Data.X509.Name.RDN.TCB
import      Armor.Grammar.Definitions
import      Armor.Grammar.Parser
open import Armor.Prelude

module Armor.Data.X509.Name.RDN.Parser where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Parser      UInt8

private
  here' = "X509: Name: RDNSequence: RDN"

[_]parse : ∀ t → Parser (Logging ∘ Dec) [ t ]RDN
[ t ]parse = parseTLV t here' _ (SetOf.parseFields here' TLV.nonempty TLV.nosubstrings ATV.parse)

parse : Parser (Logging ∘ Dec) RDN
parse = [ Tag.Sett ]parse

parseSequence : Parser (Logging ∘ Dec) RDNSequence
parseSequence = parseSeq (here' String.++ "Sequence") _ TLV.nonempty TLV.nosubstrings parse
