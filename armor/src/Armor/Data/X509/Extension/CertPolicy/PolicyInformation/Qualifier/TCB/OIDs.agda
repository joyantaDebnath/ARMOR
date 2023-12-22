open import Armor.Binary
open import Armor.Data.X690-DER.OID.Parser
open import Armor.Data.X690-DER.OID.TCB
import      Armor.Grammar.Definitions
import      Armor.Grammar.Parallel.TCB
import      Armor.Grammar.Parser
open import Armor.Prelude

module Armor.Data.X509.Extension.CertPolicy.PolicyInformation.Qualifier.TCB.OIDs where

open Armor.Grammar.Definitions  UInt8
open Armor.Grammar.Parallel.TCB UInt8
open Armor.Grammar.Parser       UInt8

CPSURILit : List UInt8
CPSURILit = # 43 ∷ # 6 ∷ # 1 ∷ # 5 ∷ # 5 ∷ # 7 ∷ # 2 ∷ [ # 1 ]

CPSURI : OIDValue CPSURILit
CPSURI = fstₚ (Success.value (toWitness{Q = Logging.val (runParser (parseOIDValue (length CPSURILit)) CPSURILit)} tt))

UserNoticeLit : List UInt8
UserNoticeLit = # 43 ∷ # 6 ∷ # 1 ∷ # 5 ∷ # 5 ∷ # 7 ∷ # 2 ∷ [ # 2 ]

UserNotice : OIDValue UserNoticeLit
UserNotice = fstₚ (Success.value (toWitness{Q = Logging.val (runParser (parseOIDValue (length UserNoticeLit)) UserNoticeLit)} tt))
