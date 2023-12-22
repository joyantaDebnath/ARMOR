open import Armor.Binary
open import Armor.Data.X509.PublicKey.Alg.ECPKParameters.ECParameters
open import Armor.Data.X509.PublicKey.Alg.ECPKParameters.TCB
open import Armor.Data.X690-DER.Null
open import Armor.Data.X690-DER.OID
open import Armor.Data.X690-DER.TLV
import      Armor.Grammar.Definitions
import      Armor.Grammar.Sum
open import Armor.Prelude

module Armor.Data.X509.PublicKey.Alg.ECPKParameters.Properties where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Sum         UInt8

iso : Iso ECPKParametersRep ECPKParameters
proj₁ iso = equivalent
proj₁ (proj₂ iso) (Sum.inj₁ x) = refl
proj₁ (proj₂ iso) (Sum.inj₂ (Sum.inj₁ x)) = refl
proj₁ (proj₂ iso) (Sum.inj₂ (Sum.inj₂ x)) = refl
proj₂ (proj₂ iso) (ecparams x) = refl
proj₂ (proj₂ iso) (namedcurve x) = refl
proj₂ (proj₂ iso) (implicitlyCA x) = refl

private
  @0 nocon : NoConfusion ECParameters (Sum OID Null)
  nocon = Sum.noconfusion{A = ECParameters} (TLV.noconfusion λ ()) (TLV.noconfusion λ ())

@0 nosubstrings : NoSubstrings ECPKParameters
nosubstrings =
  Iso.nosubstrings equivalent
    (Sum.nosubstrings TLV.nosubstrings
    (Sum.nosubstrings TLV.nosubstrings
                      TLV.nosubstrings (TLV.noconfusion λ ())) nocon)

@0 unambiguous : Unambiguous ECPKParameters
unambiguous =
  Iso.unambiguous iso
    (Sum.unambiguous ECParameters.unambiguous
      (Sum.unambiguous OID.unambiguous Null.unambiguous
        (TLV.noconfusion λ ()))
      nocon)

@0 nonmalleable : NonMalleable RawECPKParameters
nonmalleable =
  Iso.nonmalleable iso RawECPKParametersRep
    (Sum.nonmalleable{ra = RawECParameters} ECParameters.nonmalleable
    (Sum.nonmalleable{ra = RawOID} OID.nonmalleable
                                   Null.nonmalleable))

instance
  eq≋ : Eq≋ ECPKParameters
  eq≋ = Iso.isoEq≋ iso (Sum.sumEq≋ ⦃ it ⦄ ⦃ Sum.sumEq≋ ⦃ it ⦄ ⦃ it ⦄ ⦄)
