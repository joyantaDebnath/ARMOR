open import Armor.Binary
import      Armor.Grammar.Definitions.Eq
import      Armor.Grammar.Definitions.NonMalleable
import      Armor.Grammar.Option.TCB
open import Armor.Prelude

module Armor.Data.X690-DER.Default.TCB where

open Armor.Grammar.Definitions.Eq           UInt8
open Armor.Grammar.Definitions.NonMalleable UInt8
open Armor.Grammar.Option.TCB               UInt8

module _ {A : @0 List UInt8 → Set} ⦃ _ : Eq≋ A ⦄ {@0 bs' : List UInt8} (default : A bs') where
  NotDefault : ∀ {bs} → Option A bs → Set
  NotDefault none = ⊤
  NotDefault (some a) = False (_≋?_ a default)

record Default (A : @0 List UInt8 → Set) ⦃ _ : Eq≋ A ⦄ {@0 bs' : List UInt8} (default : A bs') (@0 bs : List UInt8) : Set where
  constructor mkDefault
  field
    value : Option A bs
    @0 notDefault : NotDefault default value

  getValue : Exists─ _ A
  getValue = elimOption {X = const (Exists─ _ A)} (-, default) (λ a → (─ _ , a)) value

RawDefault : ∀ {A : @0 List UInt8 → Set} ⦃ _ : Eq≋ A ⦄ → Raw A → ∀ {bs'} → (default : A bs') → Raw (Default A default)
Raw.D (RawDefault R default) = Raw.D R
Raw.to (RawDefault R default) (mkDefault none notDefault) = Raw.to R default
Raw.to (RawDefault R default) (mkDefault (some value) notDefault) = Raw.to R value
