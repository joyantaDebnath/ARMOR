open import Armor.Binary
import      Armor.Data.X509.Extension.AIA.AccessDesc.TCB.OIDs as OIDs
open import Armor.Data.X509.GeneralNames.GeneralName.TCB
open import Armor.Data.X690-DER.OID
open import Armor.Data.X690-DER.Sequence.DefinedByOID
open import Armor.Data.X690-DER.TLV.TCB
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Definitions
import      Armor.Grammar.Parallel.TCB
open import Armor.Prelude

module Armor.Data.X509.Extension.AIA.AccessDesc.TCB where

open Armor.Grammar.Definitions  UInt8
open Armor.Grammar.Parallel.TCB UInt8

supportedAccessMethod : List (Exists─ _ OIDValue)
supportedAccessMethod = (-, OIDs.OSCP) ∷ [ -, OIDs.CAIssuers ]

AccessDescParam : {@0 bs : List UInt8} → OID bs → @0 List UInt8 → Set
AccessDescParam o =
     GeneralName
  ×ₚ (λ _ → (True ((-, TLV.val o) ∈? supportedAccessMethod)))

AccessDesc : @0 List UInt8 → Set
AccessDesc = DefinedByOID AccessDescParam

RawAccessDescParam : Raw₁ RawOID AccessDescParam
Raw₁.D RawAccessDescParam _ = Raw.D RawGeneralName
Raw₁.to RawAccessDescParam _ x = Raw.to RawGeneralName (fstₚ x)

RawAccessDesc : Raw AccessDesc
RawAccessDesc = RawDefinedByOID RawAccessDescParam
