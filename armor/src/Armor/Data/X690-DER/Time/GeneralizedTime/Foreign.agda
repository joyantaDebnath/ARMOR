open import Armor.Arith
open import Armor.Binary
open import Armor.Data.X690-DER.Time.Day.TCB
open import Armor.Data.X690-DER.Time.GeneralizedTime.Parser
open import Armor.Data.X690-DER.Time.GeneralizedTime.Properties
open import Armor.Data.X690-DER.Time.GeneralizedTime.TCB
open import Armor.Data.X690-DER.Time.MDHMS.TCB
open import Armor.Data.X690-DER.Time.Month.TCB
import      Armor.Data.X690-DER.Time.Month.Properties as Month
open import Armor.Data.X690-DER.Time.TimeType.TCB
import      Armor.Data.X690-DER.Time.TimeType.Properties as TimeType
open import Armor.Data.X690-DER.Time.Year.TCB
import      Armor.Foreign.Time as Foreign
import      Armor.Grammar.Parser
open import Armor.Prelude
import      Data.Nat.Properties as Nat
open import Tactic.MonoidSolver
  using (solve ; solve-macro)

module Armor.Data.X690-DER.Time.GeneralizedTime.Foreign where

open Armor.Grammar.Parser UInt8

encodeForeignUTC : Foreign.UTCTime → List UInt8
encodeForeignUTC u =
     encodeℕ 4 (Foreign.year u)
  ++ encodeℕ 2 (Foreign.month u)
  ++ encodeℕ 2 (Foreign.day u)
  ++ encodeℕ 2 (Foreign.hour u)
  ++ encodeℕ 2 (Foreign.minute u)
  ++ encodeℕ 2 (Foreign.second u)
  ++ [ # 'Z' ]

fromForeignUTC : (u : Foreign.UTCTime) → Dec (GeneralizedTimeFields (encodeForeignUTC u))
fromForeignUTC u = case runParser parseFields (encodeForeignUTC u) ret (const _) of λ where
  (mkLogged log (no ¬p)) → no λ where
    t@(mkGeneralizedTime year mdhms bs≡) →
      contradiction (success _ _ refl t [] (++-identityʳ _)) ¬p
  (mkLogged log (yes (success prefix read read≡ value@(mkGeneralizedTime{y} year (mkMDHMS{mo}{d}{h}{mi}{s} month day dayRange hour minute sec refl) refl) suffix ps≡))) →
    let prefix≡ : Erased (y ++ (mo ++ d ++ h ++ mi ++ s) ++ [ # 'Z' ] ≡ encodeForeignUTC u)
        prefix≡ = ─
          (proj₁ (Lemmas.length-++-≡ _ _ (encodeForeignUTC u) [] ps≡
            (begin
              length (y ++ (mo ++ d ++ h ++ mi ++ s) ++ [ # 'Z' ]) ≡⟨ length-++ y ⟩
              length y + length ((mo ++ d ++ h ++ mi ++ s) ++ [ # 'Z' ])
                ≡⟨ cong₂ _+_{length y} (TimeType.bsLen year)
                     (trans (length-++ ((mo ++ d ++ h ++ mi ++ s)))
                       (cong (_+ 1) (trans (length-++ mo)
                         (cong₂ _+_ (TimeType.bsLen month)
                           (trans (length-++ d)
                             (cong₂ _+_ (TimeType.bsLen day)
                               (trans (length-++ h)
                                 (cong₂ _+_ (TimeType.bsLen hour)
                                   (trans (length-++ mi)
                                     (cong₂ _+_ (TimeType.bsLen minute) (TimeType.bsLen sec))))))))))) ⟩
              15 ∎)))
    in
    yes (subst₀! GeneralizedTimeFields (¡ prefix≡) value)

    where
    open ≡-Reasoning
