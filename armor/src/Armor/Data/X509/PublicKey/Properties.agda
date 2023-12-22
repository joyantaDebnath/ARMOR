open import Armor.Binary
open import Armor.Data.X509.PublicKey.Alg
open import Armor.Data.X509.PublicKey.Alg.TCB.OIDs
open import Armor.Data.X509.PublicKey.Val
open import Armor.Data.X509.PublicKey.TCB
open import Armor.Data.X690-DER.OID.TCB
open import Armor.Data.X690-DER.TLV
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Definitions
import      Armor.Grammar.Seq
open import Armor.Prelude

module Armor.Data.X509.PublicKey.Properties where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Seq         UInt8

iso   : Iso PublicKeyFieldsRep PublicKeyFields
proj₁ iso = equivalent
proj₁ (proj₂ iso) (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = refl
proj₂ (proj₂ iso) (mkPublicKeyFields alg key bs≡) = refl

@0 unambiguous : Unambiguous PublicKey
unambiguous =
  TLV.unambiguous
    (Iso.unambiguous iso
      (Seq.unambiguousᵈ Alg.unambiguous TLV.nosubstrings Val.unambiguous))

@0 nonmalleable : NonMalleable RawPublicKey
nonmalleable =
  TLV.nonmalleable
    (Iso.nonmalleable iso RawPublicKeyFieldsRep
      (Seq.nonmalleableᵈ{ra = RawPublicKeyAlg}{rb = RawPublicKeyVal} Alg.nonmalleable
        λ {bs}{a} → Val.nonmalleable{bs}{a}))
