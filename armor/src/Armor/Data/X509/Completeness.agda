open import Armor.Binary
open import Armor.Data.X509
import      Armor.Grammar.Definitions
import      Armor.Grammar.Parser
  hiding (module Generic)
open import Armor.Prelude

module Armor.Data.X509.Completeness where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Parser      UInt8

private 
  module Generic where
    open import Armor.Grammar.Parser.Completeness UInt8 public
    open Proofs (Logging ∘ Dec) Logging.val public

open Generic.Definitions (Logging ∘ Dec) Logging.val

@0 soundness : Sound parseCert
soundness = Generic.soundness parseCert

@0 weakCompleteness : WeaklyComplete parseCert
weakCompleteness = Generic.weakCompleteness parseCert

@0 strongCompleteness : StronglyComplete parseCert
strongCompleteness = Generic.strongCompleteness parseCert Cert.unambiguous TLV.nosubstrings

