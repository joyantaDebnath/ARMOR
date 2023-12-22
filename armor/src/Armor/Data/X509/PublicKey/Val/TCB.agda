open import Armor.Binary
open import Armor.Data.X509.PublicKey.Alg.TCB as Alg
  hiding (getOID)
import      Armor.Data.X509.PublicKey.Alg.TCB.OIDs as OIDs
open import Armor.Data.X509.PublicKey.Val.EC.TCB
open import Armor.Data.X509.PublicKey.Val.RSA.TCB
open import Armor.Data.X690-DER.BitString.TCB
open import Armor.Data.X690-DER.OID
open import Armor.Data.X690-DER.TLV.TCB
import      Armor.Grammar.Definitions.NonMalleable
import      Armor.Grammar.Sum.TCB
open import Armor.Prelude

module Armor.Data.X509.PublicKey.Val.TCB where

open Armor.Grammar.Definitions.NonMalleable UInt8
open Armor.Grammar.Sum.TCB                  UInt8

PublicKeyVal' : ∀ {@0 bs₁} → (a : PublicKeyAlg bs₁) → Dec ((-, TLV.val (Alg.getOID a)) ∈ OIDs.Supported) → @0 List UInt8 → Set
PublicKeyVal' a (no ¬p) = BitString
PublicKeyVal' a (yes (here px)) = RSABitString
PublicKeyVal' a (yes (there (here px))) = ECBitString

PublicKeyVal : ∀ {@0 bs₁} → (a : PublicKeyAlg bs₁) → @0 List UInt8 → Set
PublicKeyVal a = PublicKeyVal' a ((-, TLV.val (Alg.getOID a)) ∈? OIDs.Supported)

RawPublicKeyVal“ : Raw (Sum BitString (Sum RSABitString ECBitString))
RawPublicKeyVal“ = RawSum RawBitString (RawSum RawRSABitString RawECBitString)

RawPublicKeyVal : Raw₁ RawPublicKeyAlg PublicKeyVal
toRawPublicKeyVal : ∀ {@0 bs₁} → (a : PublicKeyAlg bs₁) → (o∈? : Dec ((-, TLV.val (Alg.getOID a)) ∈ OIDs.Supported))
                    → ∀ {@0 bs₂} → PublicKeyVal' a o∈? bs₂ → Raw₁.D RawPublicKeyVal (Raw.to RawPublicKeyAlg a)

Raw₁.D RawPublicKeyVal o = Raw.D RawPublicKeyVal“
Raw₁.to RawPublicKeyVal o p = toRawPublicKeyVal o ((-, TLV.val (Alg.getOID o)) ∈? OIDs.Supported) p

toRawPublicKeyVal a (no ¬p) p = Raw.to RawPublicKeyVal“ (inj₁ p)
toRawPublicKeyVal a (yes (here px)) p = Raw.to RawPublicKeyVal“ (inj₂ (inj₁ p))
toRawPublicKeyVal a (yes (there (here px))) p = Raw.to RawPublicKeyVal“ (inj₂ (inj₂ p))
