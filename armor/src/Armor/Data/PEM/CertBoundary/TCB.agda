open import Armor.Data.Base64.TCB
open import Armor.Data.PEM.RFC5234.TCB
open import Armor.Prelude

module Armor.Data.PEM.CertBoundary.TCB where

record CertBoundary (ctrl : String) (@0 bs : List Char) : Set where
  constructor mkCertBoundary
  field
    @0 {b e} : List Char
    @0 begin : b ≡ (String.toList $ "-----" String.++ ctrl String.++ " CERTIFICATE-----")
    @0 eol   : EOL e
    @0 bs≡   : bs ≡ b ++ e

CertHeader = CertBoundary "BEGIN"
CertFooter = CertBoundary "END"

