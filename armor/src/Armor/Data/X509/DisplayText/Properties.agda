open import Armor.Binary
open import Armor.Data.Unicode.UTF8
open import Armor.Data.Unicode.UTF16
open import Armor.Data.X509.DisplayText.TCB
open import Armor.Data.X690-DER.Strings
open import Armor.Data.X690-DER.TLV
import      Armor.Data.X690-DER.Tag as Tag
open import Armor.Data.X690-DER.SequenceOf
import      Armor.Grammar.Definitions
import      Armor.Grammar.Parallel
import      Armor.Grammar.Properties
import      Armor.Grammar.Sum
open import Armor.Prelude
open import Data.List
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Armor.Data.X509.DisplayText.Properties where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Parallel    UInt8
open Armor.Grammar.Properties  UInt8
open Armor.Grammar.Sum         UInt8

iso : Iso DisplayTextRep DisplayText
proj₁ iso = equivalent
proj₁ (proj₂ iso) (Sum.inj₁ x) = refl
proj₁ (proj₂ iso) (Sum.inj₂ (Sum.inj₁ x)) = refl
proj₁ (proj₂ iso) (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x))) = refl
proj₁ (proj₂ iso) (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ x))) = refl
proj₂ (proj₂ iso) (ia5String x) = refl
proj₂ (proj₂ iso) (visibleString x) = refl
proj₂ (proj₂ iso) (bmpString x) = refl
proj₂ (proj₂ iso) (utf8String x) = refl

@0 nonempty : NonEmpty DisplayText
nonempty =
  Iso.nonempty equivalent
    (Sum.nonempty (Parallel.nonempty₁ TLV.nonempty)
      (Sum.nonempty (Parallel.nonempty₁ TLV.nonempty)
        (Sum.nonempty (Parallel.nonempty₁ TLV.nonempty)
          (Parallel.nonempty₁ TLV.nonempty))))

@0 nosubstrings : NoSubstrings DisplayText
nosubstrings =
  Iso.nosubstrings equivalent
    (Sum.nosubstrings (Parallel.nosubstrings₁ TLV.nosubstrings)
      (Sum.nosubstrings (Parallel.nosubstrings₁ TLV.nosubstrings)
        (Sum.nosubstrings (Parallel.nosubstrings₁ TLV.nosubstrings)
          (Parallel.nosubstrings₁ TLV.nosubstrings)
          (NoConfusion.sigmaₚ₁ (TLV.noconfusion λ ())))
        (Sum.noconfusion{A = Σₚ VisibleString _}
          (NoConfusion.sigmaₚ₁ (TLV.noconfusion λ ()))
          (NoConfusion.sigmaₚ₁ (TLV.noconfusion λ ()))))
      (Sum.noconfusion{A = Σₚ IA5String _}
        (NoConfusion.sigmaₚ₁ (TLV.noconfusion λ ()))
        (Sum.noconfusion{A = Σₚ IA5String _}
          (NoConfusion.sigmaₚ₁ (TLV.noconfusion λ ()))
          (NoConfusion.sigmaₚ₁ (TLV.noconfusion λ ())))))

@0 noconfusionTLV
  : ∀ {t} {@0 A} → t ∉ Tag.IA5String ∷ Tag.VisibleString ∷ Tag.BMPString ∷ [ Tag.UTF8String ]
    → NoConfusion (TLV t A) DisplayText
noconfusionTLV{t}{A} t∉ =
  symNoConfusion{A = DisplayText}{B = TLV _ A}
    (NoConfusion.equivalent{B = TLV _ A} equivalent
      (symNoConfusion{A = TLV _ A}{B = Sum _ _}
        (Sum.noconfusion{A = TLV _ A}
          (NoConfusion.sigmaₚ₁ᵣ{A₁ = TLV _ A}
            (TLV.noconfusion (λ where refl → t∉ (here refl))))
          (Sum.noconfusion{A = TLV t A}
            (NoConfusion.sigmaₚ₁ᵣ{A₁ = TLV t A}
              (TLV.noconfusion (λ where refl → t∉ (there (here refl)))))
            (Sum.noconfusion{A = TLV t A}
              (NoConfusion.sigmaₚ₁ᵣ{A₁ = TLV t A}
                (TLV.noconfusion (λ where refl → t∉ (there (there (here refl))))))
              (NoConfusion.sigmaₚ₁ᵣ{A₁ = TLV t A}
                (TLV.noconfusion λ where refl → t∉ (there (there (there (here refl)))))))))))

@0 noconfusionSeq : ∀ {@0 A} → NoConfusion (Seq A) DisplayText
noconfusionSeq = noconfusionTLV pf
  where
  pf : Tag.Sequence  ∉ _
  pf (there (there (there (there ()))))

-- @0 noconfusionNoticeReference : NoConfusion X509.NoticeReference DisplayText
-- noconfusionNoticeReference = noconfusionTLV pf
--   where
--   pf : Tag.Sequence ∉ _
--   pf (there (there (there (there ()))))

@0 unambiguous : Unambiguous DisplayText
unambiguous =
  Iso.unambiguous iso
    (Sum.unambiguous
      (Parallel.unambiguous (TLV.unambiguous IA5String.unambiguous) λ _ → inRange-unique{A = ℕ}{B = ℕ})
      (Sum.unambiguous (Parallel.unambiguous (TLV.unambiguous VisibleString.unambiguous) (λ _ → inRange-unique{A = ℕ}{B = ℕ}))
        (Sum.unambiguous
          (Parallel.unambiguous
            (TLV.unambiguous (IList.unambiguous UTF16.BMP.unambiguous UTF16.BMP.nonempty UTF16.BMP.nosubstrings))
            λ _ → inRange-unique{A = ℕ}{B = ℕ})
          (Parallel.unambiguous (TLV.unambiguous UTF8.unambiguous) (λ _ → inRange-unique{A = ℕ}{B = ℕ}))
          (NoConfusion.sigmaₚ₁ (TLV.noconfusion λ ())))
        (Sum.noconfusion{A = Σₚ _ _}
          (NoConfusion.sigmaₚ₁ (TLV.noconfusion λ ()))
          (NoConfusion.sigmaₚ₁ (TLV.noconfusion λ ()))))
      (Sum.noconfusion {A = Σₚ _ _}
        (NoConfusion.sigmaₚ₁ (TLV.noconfusion λ ()))
        (Sum.noconfusion {A = Σₚ _ _}
          (NoConfusion.sigmaₚ₁ (TLV.noconfusion λ ()))
          (NoConfusion.sigmaₚ₁ (TLV.noconfusion λ ())))))
  where
  open import Armor.Grammar.IList UInt8


@0 nonmalleable : NonMalleable RawDisplayText
nonmalleable = Iso.nonmalleable iso RawDisplayTextRep nm
  where
  nm : NonMalleable RawDisplayTextRep
  nm =
     Sum.nonmalleable
       (Parallel.nonmalleable₁ RawIA5String IA5String.nonmalleable λ _ → inRange-unique{A = ℕ}{B = ℕ})
    (Sum.nonmalleable
      (Parallel.nonmalleable₁ RawVisibleString VisibleString.nonmalleable λ _ → inRange-unique{A = ℕ}{B = ℕ})
    (Sum.nonmalleable
      (Parallel.nonmalleable₁ RawBMPString BMPString.nonmalleable λ _ → inRange-unique{A = ℕ}{B = ℕ})
      (Parallel.nonmalleable₁ RawUTF8String UTF8String.nonmalleable λ _ → inRange-unique{A = ℕ}{B = ℕ})))

instance
  DisplayTextEq : Eq (Exists─ _ DisplayText)
  DisplayTextEq =
    Iso.isoEq iso
      (Sum.sumEq ⦃ Parallel.eqΣₚ it λ a → record { _≟_ = λ x y → yes (inRange-unique{A = ℕ}{B = ℕ} x y) } ⦄
        ⦃ Sum.sumEq ⦃ Parallel.eqΣₚ it λ a → record { _≟_ = λ x y → yes (inRange-unique{A = ℕ}{B = ℕ} x y) } ⦄
            ⦃ Sum.sumEq ⦃ Parallel.eqΣₚ it λ a → record { _≟_ = λ x y → yes (inRange-unique{A = ℕ}{B = ℕ} x y) } ⦄
                ⦃ Parallel.eqΣₚ (TLV.eqTLV ⦃ UTF8.UTF8Eq ⦄) λ a → record { _≟_ = λ x y → yes (inRange-unique{A = ℕ}{B = ℕ} x y) } ⦄  ⦄ ⦄)

  eq≋ : Eq≋ DisplayText
  eq≋ = Eq⇒Eq≋ it
