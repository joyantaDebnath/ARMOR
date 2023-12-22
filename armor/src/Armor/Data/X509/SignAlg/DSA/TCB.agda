open import Armor.Binary
open import Armor.Data.X690-DER.Null.TCB
import      Armor.Data.X509.SignAlg.TCB.OIDs as OIDs
open import Armor.Data.X690-DER.OID
open import Armor.Data.X690-DER.Sequence.DefinedByOID.TCB
open import Armor.Data.X690-DER.TLV.TCB
import      Armor.Grammar.Definitions
open import Armor.Prelude

module Armor.Data.X509.SignAlg.DSA.TCB where

open Armor.Grammar.Definitions  UInt8

-- TODO: Previously we had the parameter as an explicit null. The documentation
-- says it must be absent. Which is it?

DSAParams' : ∀ {@0 bs} → (o : OID bs) → Dec ((-, TLV.val o) ∈ OIDs.DSA.Supported) → @0 List UInt8 → Set
DSAParams' o (no ¬p) bs = ⊥
DSAParams' o (yes p) bs = Erased (bs ≡ [])

DSAParams : AnyDefinedByOID
DSAParams o = DSAParams' o ((-, TLV.val o) ∈? OIDs.DSA.Supported)

RawDSAParamsRep : Raw (λ bs → Erased (bs ≡ []))
RawDSAParamsRep = RawSubSingleton

RawDSAParams : Raw₁ RawOID DSAParams
toRawDSAParams : ∀ {@0 bs} → (o : OID bs) → (o∈? : Dec ((-, TLV.val o) ∈ OIDs.DSA.Supported))
                   → ∀ {@0 bs'} → DSAParams' o o∈? bs' → Raw₁.D RawDSAParams (Raw.to RawOID o)

Raw₁.D RawDSAParams o = Raw.D RawDSAParamsRep
Raw₁.to RawDSAParams o p = toRawDSAParams o ((-, TLV.val o) ∈? OIDs.DSA.Supported) p

toRawDSAParams o (yes p₁) p = Raw.to RawDSAParamsRep p

DSA : @0 List UInt8 → Set
DSA = DefinedByOID DSAParams

RawDSA : Raw DSA
RawDSA = RawDefinedByOID RawDSAParams

-- erase
--   : ∀ {@0 bs} → Supported bs
--     → DefinedByOID
--         (λ o → (Erased ∘ OctetStringValue) ×ₚ const (True ((-, TLV.val o) ∈? supportedSignAlgOIDs)))
--         bs
-- erase (Sum.inj₁ (mkTLV len (mkOIDDefinedFields algOID (mk×ₚ _ ≋-refl) bs≡₁) len≡ bs≡)) =
--   mkTLV len (mkOIDDefinedFields algOID (mk×ₚ (─ self) tt) bs≡₁) len≡ bs≡
-- erase (Sum.inj₂ (Sum.inj₁ (mkTLV len (mkOIDDefinedFields algOID (mk×ₚ _ ≋-refl) bs≡₁) len≡ bs≡))) =
--   mkTLV len (mkOIDDefinedFields algOID (mk×ₚ (─ self) tt) bs≡₁) len≡ bs≡
-- erase (Sum.inj₂ (Sum.inj₂ (mkTLV len (mkOIDDefinedFields algOID (mk×ₚ _ ≋-refl) bs≡₁) len≡ bs≡))) =
--   mkTLV len (mkOIDDefinedFields algOID (mk×ₚ (─ self) tt) bs≡₁) len≡ bs≡
