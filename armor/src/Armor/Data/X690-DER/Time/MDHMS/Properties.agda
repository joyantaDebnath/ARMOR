open import Armor.Binary
open import Armor.Data.X690-DER.Time.Day
open import Armor.Data.X690-DER.Time.Hour
open import Armor.Data.X690-DER.Time.Minute
open import Armor.Data.X690-DER.Time.MDHMS.TCB
open import Armor.Data.X690-DER.Time.Month
open import Armor.Data.X690-DER.Time.TimeType
open import Armor.Data.X690-DER.Time.Sec
import      Armor.Grammar.Definitions
import      Armor.Grammar.Parallel
import      Armor.Grammar.Seq
open import Armor.Prelude

module Armor.Data.X690-DER.Time.MDHMS.Properties where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Parallel    UInt8
open Armor.Grammar.Seq         UInt8

@0 length≡ : ∀ {@0 bs} → MDHMS bs → length bs ≡ 10
length≡ {bs} (mkMDHMS{mo}{da}{ho}{mi}{se} month day dayRange hour minute sec bs≡) =
  begin
    length bs
      ≡⟨ cong length bs≡ ⟩
    length (mo ++ da ++ ho ++ mi ++ se)
      ≡⟨ length-++ mo ⟩
    length mo + length (da ++ ho ++ mi ++ se)
      ≡⟨ cong₂ _+_
           (TimeType.bsLen month)
           (begin
             length (da ++ ho ++ mi ++ se) ≡⟨ length-++ da ⟩
             length da + length (ho ++ mi ++ se)
               ≡⟨ cong₂ _+_
                    (TimeType.bsLen day)
                    (begin
                      length (ho ++ mi ++ se) ≡⟨ length-++ ho ⟩
                      length ho + length (mi ++ se)
                        ≡⟨ cong₂ _+_
                             (TimeType.bsLen hour)
                             (begin
                               length (mi ++ se) ≡⟨ length-++ mi ⟩
                               length mi + length se
                                 ≡⟨ cong₂ _+_ (TimeType.bsLen minute) (TimeType.bsLen sec) ⟩
                               4 ∎) ⟩
                      6 ∎) ⟩
             8 ∎) ⟩
    10 ∎
  where
  open ≡-Reasoning

@0 nosubstrings : NoSubstrings MDHMS
nosubstrings =
  Iso.nosubstrings equivalent
    (Seq.nosubstrings
      (Seq.nosubstringsᵈ TimeType.nosubstrings TimeType.unambiguous
        (λ _ → Parallel.nosubstrings₁ TimeType.nosubstrings))
      (Seq.nosubstrings TimeType.nosubstrings (Seq.nosubstrings TimeType.nosubstrings TimeType.nosubstrings)))

iso : Iso MDHMSRep MDHMS
proj₁ iso = equivalent
proj₁ (proj₂ iso) (mk&ₚ{bs₂ = bs₃} (mk&ₚ{bs₁}{bs₂} mo (mk×ₚ d (─ dr)) refl) (mk&ₚ h (mk&ₚ mi s refl) refl) refl) =
  let p : Erased ((bs₁ ++ bs₂) ++ bs₃ ≡ bs₁ ++ bs₂ ++ bs₃)
      p = ─ (++-assoc bs₁ bs₂ bs₃)
  in
  subst₀ (λ eq →   mk&ₚ (mk&ₚ mo (mk×ₚ d (─ dr)) refl) (mk&ₚ h (mk&ₚ mi s refl) refl) eq
                 ≡ mk&ₚ (mk&ₚ mo (mk×ₚ d (─ dr)) refl) (mk&ₚ h (mk&ₚ mi s refl) refl) refl)
    (sym $ trans-symʳ (¡ p)) refl
proj₂ (proj₂ iso) (mkMDHMS{mo}{d}{h}{mi}{s} month day dayRange hour minute sec refl) =
  let p : Erased ((mo ++ d) ++ h ++ mi ++ s ≡ mo ++ d ++ h ++ mi ++ s)
      p = ─ (++-assoc mo d _)
  in
  subst₀ (λ eq →   mkMDHMS month day dayRange hour minute sec eq
                 ≡ mkMDHMS month day dayRange hour minute sec refl)
    (sym (trans-symˡ (¡ p))) refl

@0 unambiguous : Unambiguous MDHMS
unambiguous =
  Iso.unambiguous iso
    (Seq.unambiguous
      (Seq.unambiguousᵈ TimeType.unambiguous TimeType.nosubstrings
        (λ a → Parallel.unambiguous TimeType.unambiguous (λ _ → erased-unique ≤-unique)))
      (Seq.nosubstringsᵈ TimeType.nosubstrings TimeType.unambiguous
        (λ _ → Parallel.nosubstrings₁ TimeType.nosubstrings))
    (Seq.unambiguous TimeType.unambiguous TimeType.nosubstrings
    (Seq.unambiguous TimeType.unambiguous TimeType.nosubstrings TimeType.unambiguous)))

@0 nonmalleable : NonMalleable RawMDHMS
nonmalleable = Iso.nonmalleable iso RawMDHMSRep nm
  where
  nmDOM : NonMalleable₁{R = RawMonth} RawDOM
  nmDOM (mk×ₚ d₁ (─ d₁range)) (mk×ₚ d₂ (─ d₂range)) eq =
    case TimeType.nonmalleable d₁ d₂ eq ret (const _) of λ where
      refl → case ‼ ≤-unique d₁range d₂range ret (const _) of λ where
        refl → refl

  nm : NonMalleable RawMDHMSRep
  nm =
     Seq.nonmalleable
       (Seq.nonmalleableᵈ{rb = RawDOM} TimeType.nonmalleable (λ {bs}{a}{bs₁}{bs₂} → nmDOM{bs}{a}{bs₁}{bs₂}))
    (Seq.nonmalleable TimeType.nonmalleable
    (Seq.nonmalleable TimeType.nonmalleable
                      TimeType.nonmalleable))

instance
  eq≋ : Eq≋ MDHMS
  eq≋ = Iso.isoEq≋ iso
          (Seq.eq≋&ₚ
            (Seq.eq≋&ₚᵈ it
              (λ mo → Parallel.eq≋Σₚ it
               λ da → record { _≟_ = λ x y → yes (erased-unique ≤-unique x y) }))
          (Seq.eq≋&ₚ it
          (Seq.eq≋&ₚ it it)))

  eq : Eq (Exists─ (List UInt8) MDHMS)
  eq = Eq≋⇒Eq eq≋
