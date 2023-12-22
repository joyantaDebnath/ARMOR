open import Armor.Binary
open import Armor.Data.X509.Extension.BC.TCB
open import Armor.Data.X690-DER.Boool
open import Armor.Data.X690-DER.Default
open import Armor.Data.X690-DER.Int
open import Armor.Data.X690-DER.Sequence
open import Armor.Data.X690-DER.TLV
import      Armor.Grammar.Definitions
import      Armor.Grammar.Option
import      Armor.Grammar.Properties
import      Armor.Grammar.Seq
open import Armor.Prelude

module Armor.Data.X509.Extension.BC.Properties where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Option      UInt8
open Armor.Grammar.Properties  UInt8
open Armor.Grammar.Seq         UInt8

Rep = &ₚ (Default Boool falseBoool) (Option Int)

equivalent : Equivalent Rep BCFieldsSeqFields
proj₁ equivalent (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = mkBCFieldsSeqFields fstₚ₁ sndₚ₁ bs≡
proj₂ equivalent (mkBCFieldsSeqFields bcca bcpathlen bs≡) = mk&ₚ bcca bcpathlen bs≡

iso : Iso Rep BCFieldsSeqFields
proj₁ iso = equivalent
proj₁ (proj₂ iso) (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = refl
proj₂ (proj₂ iso) (mkBCFieldsSeqFields bcca bcpathlen bs≡) = refl

@0 unambiguous : Unambiguous BCFields
unambiguous =
  TLV.unambiguous
    (TLV.unambiguous
      (Iso.unambiguous iso ua))
  where
  ua : Unambiguous Rep
  ua =
    Sequence.unambiguousDefaultOption falseBoool
      Boool.unambiguous TLV.nosubstrings TLV.nonempty
      Int.unambiguous TLV.nonempty
      (TLV.noconfusion λ ())

@0 nonmalleable : NonMalleable RawBCFields
nonmalleable =
  TLV.nonmalleable (TLV.nonmalleable
    (Iso.nonmalleable iso RawBCFieldsSeqFieldsRep
      (Seq.nonmalleable (Default.nonmalleable _ Boool.nonmalleable)
                        (Option.nonmalleable _ Int.nonmalleable))))
