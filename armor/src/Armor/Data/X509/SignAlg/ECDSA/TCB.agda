open import Armor.Binary
import      Armor.Data.X509.SignAlg.TCB.OIDs as OIDs
open import Armor.Data.X690-DER.OID
open import Armor.Data.X690-DER.Sequence.DefinedByOID
open import Armor.Data.X690-DER.TLV.TCB
import      Armor.Grammar.Definitions.NonMalleable
open import Armor.Prelude

module Armor.Data.X509.SignAlg.ECDSA.TCB where

open Armor.Grammar.Definitions.NonMalleable UInt8

ECDSAParams' : ∀ {@0 bs} → (o : OID bs) → Dec ((-, TLV.val o) ∈ OIDs.ECDSA.Supported) → @0 List UInt8 → Set
ECDSAParams' o (no ¬p) bs = ⊥
ECDSAParams' o (yes p) bs = Erased (bs ≡ [])

ECDSAParams : AnyDefinedByOID
ECDSAParams o = ECDSAParams' o ((-, TLV.val o) ∈? OIDs.ECDSA.Supported)

RawECDSAParamsRep : Raw (λ bs → Erased (bs ≡ []))
RawECDSAParamsRep = RawSubSingleton

RawECDSAParams : Raw₁ RawOID ECDSAParams
toRawECDSAParams : ∀ {@0 bs} → (o : OID bs) → (o∈? : Dec ((-, TLV.val o) ∈ OIDs.ECDSA.Supported))
                   → ∀ {@0 bs'} → ECDSAParams' o o∈? bs' → Raw₁.D RawECDSAParams (Raw.to RawOID o)

Raw₁.D RawECDSAParams o = ⊤
Raw₁.to RawECDSAParams o p = toRawECDSAParams o ((-, TLV.val o) ∈? OIDs.ECDSA.Supported) p

toRawECDSAParams o (yes p₁) p = tt

ECDSA : @0 List UInt8 → Set
ECDSA = DefinedByOID ECDSAParams

RawECDSA : Raw ECDSA
RawECDSA = RawDefinedByOID RawECDSAParams

-- erase
--   : ∀ {@0 bs} → Supported bs
--     → DefinedByOID
--         (λ o → (Erased ∘ OctetStringValue) ×ₚ const (True ((-, TLV.val o) ∈? supportedSignAlgOIDs)))
--         bs
-- erase (Sum.inj₁ (mkTLV len (mkOIDDefinedFields algOID (mk×ₚ _ ≋-refl) bs≡₁) len≡ bs≡)) =
--   mkTLV len (mkOIDDefinedFields algOID (mk×ₚ (─ self) tt) bs≡₁) len≡ bs≡
-- erase (Sum.inj₂ (Sum.inj₁ (mkTLV len (mkOIDDefinedFields algOID (mk×ₚ _ ≋-refl) bs≡₁) len≡ bs≡))) =
--   mkTLV len (mkOIDDefinedFields algOID (mk×ₚ (─ self) tt) bs≡₁) len≡ bs≡
-- erase (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ (mkTLV len (mkOIDDefinedFields algOID (mk×ₚ _ ≋-refl) bs≡₁) len≡ bs≡)))) =
--   mkTLV len (mkOIDDefinedFields algOID (mk×ₚ (─ self) tt) bs≡₁) len≡ bs≡
-- erase (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ (mkTLV len (mkOIDDefinedFields algOID (mk×ₚ _ ≋-refl) bs≡₁) len≡ bs≡))))) =
--   mkTLV len (mkOIDDefinedFields algOID (mk×ₚ (─ self) tt) bs≡₁) len≡ bs≡
-- erase (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (mkTLV len (mkOIDDefinedFields algOID (mk×ₚ _ ≋-refl) bs≡₁) len≡ bs≡))))) =
--   mkTLV len (mkOIDDefinedFields algOID (mk×ₚ (─ self) tt) bs≡₁) len≡ bs≡
