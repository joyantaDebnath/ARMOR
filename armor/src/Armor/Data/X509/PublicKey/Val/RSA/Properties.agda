open import Armor.Binary
open import Armor.Data.X509.PublicKey.Val.RSA.TCB
open import Armor.Data.X509.PublicKey.Val.RSA.Ints
open import Armor.Data.X690-DER.TLV
import      Armor.Grammar.Definitions
import      Armor.Grammar.Seq
open import Armor.Prelude

module Armor.Data.X509.PublicKey.Val.RSA.Properties where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Seq         UInt8

iso : Iso RSABitStringFieldsRep RSABitStringFields
proj₁ iso = equivalent
proj₁ (proj₂ iso) (mk&ₚ (─ refl) sndₚ₁ bs≡) = refl
proj₂ (proj₂ iso) (mkRSABitStringFields self rsane bs≡) = refl

@0 nosubstrings : NoSubstrings RSABitStringFields
nosubstrings =
  Iso.nosubstrings equivalent
    (Seq.nosubstrings (λ where _ (─ refl) (─ refl) → refl) TLV.nosubstrings)

@0 unambiguousFields : Unambiguous RSABitStringFields
unambiguousFields =
  Iso.unambiguous iso
    (Seq.unambiguous
      (erased-unique ≡-unique) (λ where _ (─ refl) (─ refl) → refl)
      Ints.unambiguous)

@0 unambiguous : Unambiguous RSABitString
unambiguous = TLV.unambiguous unambiguousFields

@0 nonmalleableFields : NonMalleable RawRSABitStringFields
nonmalleableFields =
  Iso.nonmalleable iso RawRSABitStringFieldsRep
    (Seq.nonmalleable
      (subsingleton⇒nonmalleable (λ where (─ _ , ─ refl) (─ _ , ─ refl) → refl))
      Ints.nonmalleable)

@0 nonmalleable : NonMalleable RawRSABitString
nonmalleable = TLV.nonmalleable nonmalleableFields
