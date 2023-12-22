open import Armor.Data.Base64.TCB
import      Armor.Grammar.Definitions
import      Armor.Grammar.Sum
open import Armor.Prelude

module Armor.Data.PEM.RFC5234.TCB where

open Armor.Grammar.Definitions Char
open Armor.Grammar.Sum         Char

WSP = Sum (λ x → Erased (x ≡ [ ' ' ])) (λ x → Erased (x ≡ [ '\t' ]))

data EOL : @0 List Char → Set where
  crlf : EOL ('\r' ∷ [ '\n' ])
  cr   : EOL [ '\r' ]
  lf   : EOL [ '\n' ]
