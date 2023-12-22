open import Armor.Binary
open import Armor.Data.X690-DER.Time.Day
open import Armor.Data.X690-DER.Time.Hour
open import Armor.Data.X690-DER.Time.Minute
open import Armor.Data.X690-DER.Time.MDHMS.TCB
open import Armor.Data.X690-DER.Time.Month
open import Armor.Data.X690-DER.Time.TimeType
open import Armor.Data.X690-DER.Time.Sec
import      Armor.Grammar.Parallel
import      Armor.Grammar.Parser
import      Armor.Grammar.Seq
open import Armor.Prelude

module Armor.Data.X690-DER.Time.MDHMS.Parser where

open Armor.Grammar.Parallel UInt8
open Armor.Grammar.Parser   UInt8
open Armor.Grammar.Seq      UInt8

parse : Parser (Logging ∘ Dec) MDHMS
parse = parseEquivalent equivalent p
  where
  p : Parser (Logging ∘ Dec) MDHMSRep
  p =  parse& (Seq.nosubstringsᵈ TimeType.nosubstrings TimeType.unambiguous
                (λ a → Parallel.nosubstrings₁ TimeType.nosubstrings))
      (parse&ᵈ TimeType.nosubstrings TimeType.unambiguous Month.parse λ r a →
        parseSigma TimeType.nosubstrings TimeType.unambiguous Day.parse (λ _ → erased? (_ ≤? _)))
      (parse& TimeType.nosubstrings Hour.parse
      (parse& TimeType.nosubstrings Minute.parse
                                      Sec.parse))
