open import Armor.Binary
open import Armor.Data.X690-DER.OID.Parser
open import Armor.Data.X690-DER.OID.TCB
import      Armor.Grammar.Definitions
import      Armor.Grammar.Parallel
import      Armor.Grammar.Parser
open import Armor.Prelude

module Armor.Data.X509.Extension.AIA.AccessDesc.TCB.OIDs where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Parallel    UInt8
open Armor.Grammar.Parser      UInt8

OSCPLit : List UInt8
OSCPLit = # 43 ∷ # 6 ∷ # 1 ∷ # 5 ∷ # 5 ∷ # 7 ∷ # 48 ∷ [ # 1 ]

OSCP : OIDValue OSCPLit
OSCP = fstₚ (Success.value (toWitness{Q = Logging.val (runParser (parseOIDValue (length OSCPLit)) OSCPLit)} tt))


CAIssuersLit : List UInt8
CAIssuersLit = # 43 ∷ # 6 ∷ # 1 ∷ # 5 ∷ # 5 ∷ # 7 ∷ # 48 ∷ [ # 2 ]

CAIssuers : OIDValue CAIssuersLit
CAIssuers = fstₚ (Success.value (toWitness{Q = Logging.val (runParser (parseOIDValue (length CAIssuersLit)) CAIssuersLit)} tt))
