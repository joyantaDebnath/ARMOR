open import Armor.Binary
open import Armor.Prelude
import      Armor.Grammar.Definitions.NonMalleable
import      Data.Nat.Properties as Nat

module Armor.Data.X690-DER.Length.TCB where

open Armor.Grammar.Definitions.NonMalleable UInt8
  using (Raw)

-- https://www.itu.int/rec/T-REC-X.690-202102-I/en
-- 10.1 Length forms
-- The definite form of length encoding shall be used, encoded in the minimum number of octets. [Contrast with 8.1.3.2 b).]
-- 8.1.3.3 For the definite form, the length octets shall consist of one or more octets, and shall represent the number of octets
-- in the contents octets using either the short form (see 8.1.3.4) or the long form (see 8.1.3.5) as a sender's option.
-- NOTE – The short form can only be used if the number of octets in the contents octets is less than or equal to 127.
-- 8.1.3.4 In the short form, the length octets shall consist of a single octet in which bit 8 is zero and bits 7 to 1 encode the
-- number of octets in the contents octets (which may be zero), as an unsigned binary integer with bit 7 as the most significant
-- bit.
-- 8.1.3.5 In the long form, the length octets shall consist of an initial octet and one or more subsequent octets. The initial
-- octet shall be encoded as follows:
-- a) bit 8 shall be one;
-- b) bits 7 to 1 shall encode the number of subsequent octets in the length octets, as an unsigned binary integer with
-- bit 7 as the most significant bit;
-- c) the value 111111112 shall not be used.
-- NOTE 1 – This restriction is introduced for possible future extension.
-- Bits 8 to 1 of the first subsequent octet, followed by bits 8 to 1 of the second subsequent octet, followed in turn by bits 8 to 1
-- of each further octet up to and including the last subsequent octet, shall be the encoding of an unsigned binary integer equal
-- to the number of octets in the contents octets, with bit 8 of the first subsequent octet as the most significant bit.

record Short (@0 bs : List UInt8) : Set where
  constructor mkShort
  field
    l : UInt8
    @0 l<128 : toℕ l < 128
    @0 bs≡ : bs ≡ [ l ]

-- Needs to be proof irrelevant (UP)
MinRepLong : UInt8 → List UInt8 → Set
MinRepLong lₕ lₜ =
  if ⌊ lₜ ≟ [] ⌋ then toℕ lₕ ≥ 128 else ⊤

record Long (@0 bs : List UInt8) : Set where
  constructor mkLong
  field
    l : UInt8
    @0 l>128 : 128 < toℕ l
    lₕ : UInt8
    @0 lₕ≢0 : toℕ lₕ > 0
    lₜ : List UInt8
    @0 lₜLen : length lₜ ≡ toℕ l - 129
    @0 lₕₜMinRepLong : MinRepLong lₕ lₜ
    @0 bs≡ : bs ≡ l ∷ lₕ ∷ lₜ

data Length : (@0 _ : List UInt8) → Set where
  short : ∀ {@0 bs} → Short bs → Length bs
  long  : ∀ {@0 bs} → Long  bs → Length bs

getLengthRaw : List UInt8 → ℕ
getLengthRaw = unsigned

getLength : ∀ {@0 bs} → Length bs → ℕ
getLength {bs} (short (mkShort l l<128 bs≡)) = toℕ l
getLength {bs} (long (mkLong l l>128 lₕ lₕ≢0 lₜ lₜLen _ bs≡)) = getLengthRaw (lₕ ∷ lₜ)

toLength : (n : Fin 128) → Length ([ Fin.inject≤ n (toWitness{Q = _ ≤? _} tt) ])
toLength n = short (mkShort c c< refl)
  where
  c : UInt8
  c = Fin.inject≤ n (toWitness{Q = _ ≤? _} tt)

  c< : toℕ c < 128
  c< = Nat.≤-trans
         (s≤s (Lemmas.≡⇒≤ (Fin.toℕ-inject≤ n (toWitness{Q = _ ≤? _} tt))))
         (Nat.≤-trans
           (Fin.toℕ<n n)
           Nat.≤-refl)

-- for nonmalleability
RawLength : Raw Length
Raw.D RawLength = ℕ
Raw.to RawLength = getLength
