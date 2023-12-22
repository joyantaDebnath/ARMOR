open import Armor.Binary
open import Armor.Data.X509.PublicKey.Alg.TCB as Alg
  hiding (getOID)
open import Armor.Data.X509.PublicKey.Alg.TCB.OIDs
open import Armor.Data.X509.PublicKey.Val.TCB
open import Armor.Data.X690-DER.OID.TCB
open import Armor.Data.X690-DER.TLV.TCB
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Definitions.Iso
import      Armor.Grammar.Definitions.NonMalleable
import      Armor.Grammar.Seq.TCB
open import Armor.Prelude

module Armor.Data.X509.PublicKey.TCB where

open Armor.Grammar.Definitions.Iso          UInt8
open Armor.Grammar.Definitions.NonMalleable UInt8
open Armor.Grammar.Seq.TCB                  UInt8

-- https://datatracker.ietf.org/doc/html/rfc5280#section-4.1

--    SubjectPublicKeyInfo  ::=  SEQUENCE  {
--         algorithm            AlgorithmIdentifier,
--         subjectPublicKey     BIT STRING  }
        
record PublicKeyFields (@0 bs : List UInt8) : Set where
  constructor mkPublicKeyFields
  field
    @0 {a p} : List UInt8
    alg : PublicKeyAlg a
    key : PublicKeyVal alg p
    @0 bs≡ : bs ≡ a ++ p

PublicKeyFieldsRep : @0 List UInt8 → Set
PublicKeyFieldsRep = &ₚᵈ PublicKeyAlg PublicKeyVal

equivalent : Equivalent PublicKeyFieldsRep PublicKeyFields
proj₁ equivalent (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = mkPublicKeyFields fstₚ₁ sndₚ₁ bs≡
proj₂ equivalent (mkPublicKeyFields alg key bs≡) = mk&ₚ alg key bs≡

RawPublicKeyFieldsRep : Raw PublicKeyFieldsRep
RawPublicKeyFieldsRep = Raw&ₚᵈ RawPublicKeyAlg RawPublicKeyVal

RawPublicKeyFields : Raw PublicKeyFields
RawPublicKeyFields =
  Iso.raw equivalent RawPublicKeyFieldsRep

PublicKey = TLV Tag.Sequence PublicKeyFields

RawPublicKey : Raw PublicKey
RawPublicKey = RawTLV _ RawPublicKeyFields

getOID : ∀ {@0 bs} → (pk : PublicKey bs) → OID _
getOID x = Alg.getOID (PublicKeyFields.alg (TLV.val x))

