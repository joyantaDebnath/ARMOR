open import Armor.Binary
open import Armor.Data.X509.Validity.Time.TCB
open import Armor.Data.X690-DER.TLV
open import Armor.Data.X690-DER.Time.GeneralizedTime
open import Armor.Data.X690-DER.Time.UTCTime
import      Armor.Grammar.Sum
import      Armor.Grammar.Definitions
open import Armor.Prelude

module Armor.Data.X509.Validity.Time.Ordering where

open Armor.Grammar.Sum         UInt8
open Armor.Grammar.Definitions UInt8

infix 4 _Time≤_

_Time≤_ : {@0 bs₁ bs₂ : List UInt8} → (t₁ : Time bs₁) (t₂ : Time bs₂) → Set
t₁ Time≤ t₂ = TLV.val (toGeneralizedTime t₁) GeneralizedTimeFields≤ TLV.val (toGeneralizedTime t₂)

_Time≤?_ : ∀ {@0 bs₁ bs₂} → (t₁ : Time bs₁) (t₂ : Time bs₂) → Dec (t₁ Time≤ t₂)
t₁ Time≤? t₂ = TLV.val (toGeneralizedTime t₁) GeneralizedTime.≤? TLV.val (toGeneralizedTime t₂)
