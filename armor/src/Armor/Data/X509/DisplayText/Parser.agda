open import Armor.Binary
open import Armor.Data.Unicode
open import Armor.Data.X509.DisplayText.TCB
open import Armor.Data.X690-DER.Strings
open import Armor.Data.X690-DER.TLV
import      Armor.Grammar.Parser
open import Armor.Prelude

module Armor.Data.X509.DisplayText.Parser where

open Armor.Grammar.Parser UInt8

private
  here' = "X509: DisplayText"

parseDisplayText : Parser (Logging ∘ Dec) DisplayText
runParser parseDisplayText xs = do
  no ¬ia5String ←
    runParser (parseTLVSizeBound IA5StringValue.size IA5String.sizeUnique 1 200 (here' String.++ ": IA5String") parseIA5String) xs
    where yes b → return (yes (mapSuccess (λ {bs} → ia5String{bs}) b))
  no ¬visibleString ←
    runParser (parseTLVSizeBound VisibleStringValue.size VisibleString.sizeUnique 1 200 (here' String.++ ": VisibleString") parseVisibleString) xs
    where yes b → return (yes (mapSuccess (λ {bs} → visibleString{bs}) b))
  no ¬bmp ←
    runParser (parseTLVSizeBound UTF16.size UTF16.sizeUnique 1 200 (here' String.++ ": BMPString") parseBMPString) xs
    where yes b → return (yes (mapSuccess (λ {bs} → bmpString{bs}) b))
  no ¬utf8 ←
    runParser (parseTLVSizeBound UTF8.size UTF8.sizeUnique 1 200 (here' String.++ ": UTF8String") parseUTF8String) xs
    where yes u → return (yes (mapSuccess (λ {bs} → utf8String{bs}) u))
  return ∘ no $ λ where
    (success prefix read read≡ (ia5String x) suffix ps≡) →
      contradiction (success _ _ read≡ x _ ps≡) ¬ia5String
    (success prefix read read≡ (visibleString x) suffix ps≡) →
      contradiction (success _ _ read≡ x _ ps≡) ¬visibleString
    (success prefix read read≡ (bmpString x) suffix ps≡) →
      contradiction (success _ _ read≡ x _ ps≡) ¬bmp
    (success prefix read read≡ (utf8String x) suffix ps≡) →
      contradiction (success _ _ read≡ x _ ps≡) ¬utf8
