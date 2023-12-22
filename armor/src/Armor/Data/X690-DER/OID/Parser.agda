open import Armor.Prelude

open import Armor.Binary
open import Armor.Data.X690-DER.Length
open import Armor.Data.X690-DER.OID.TCB
open import Armor.Data.X690-DER.OID.Properties
open import Armor.Data.X690-DER.SequenceOf
open import Armor.Data.X690-DER.TLV
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Definitions
import      Armor.Grammar.Parallel
import      Armor.Grammar.Parser
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Armor.Data.X690-DER.OID.Parser where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Parallel    UInt8
open Armor.Grammar.Parser      UInt8

module parseOIDSub where
  here' = "parseOIDSub"

  parseOIDSub : Parser (Logging ∘ Dec) OIDSub
  runParser parseOIDSub xs
    with runParser (parseWhileₜ ((_≥? 128) ∘ toℕ)) xs
  ... | no  ¬parse = do
    tell $ here' String.++ ": underflow"
    return ∘ no $ ‼ go
    where
    @0 go : ¬ Success OIDSub xs
    go (success ._ read@._ refl (mkOIDSub lₚ lₚ≥128 lₑ lₑ<128 leastDigs refl) suffix refl) =
      contradiction (success (lₚ ∷ʳ lₑ) read refl (mkParseWhile lₚ lₑ lₚ≥128 (<⇒≱ lₑ<128) refl) suffix refl) ¬parse
  ... | yes (success ._ _ read≡ (mkParseWhile lₚ lₑ lₚ≥128 ¬lₑ≥128 refl) suffix refl)
    with lₚ
  ... | [] = return (yes (success [ lₑ ] _ read≡ (mkOIDSub [] All.[] lₑ (≰⇒> ¬lₑ≥128) tt refl) suffix refl))
  ... | lₚ'@(l ∷ lₚ)
    with toℕ l >? 128
  ... | no  l≯128 = do
    tell $ here' String.++ ": leading byte has value 0 (non-minimal repr.)"
    return ∘ no $ ‼ go
    where
    @0 go : ¬ Success OIDSub (lₚ' ∷ʳ lₑ ++ suffix)
    go (success .([] ∷ʳ lₑ1) _ read≡ (mkOIDSub [] lₚ1≥128 lₑ1 lₑ1<128 leastDigs1 refl) .((lₚ ++ [ lₑ ]) ++ suffix) refl) =
      contradiction lₑ1<128 (≤⇒≯ (proj₁ (All.uncons lₚ≥128)))
    go (success .((x ∷ lₚ1) ∷ʳ lₑ1) _ read≡ (mkOIDSub (x ∷ lₚ1) lₚ1≥128 lₑ1 lₑ1<128 leastDigs1 refl) suffix1 ps≡1) =
      contradiction (subst (λ y → 128 < toℕ y) (∷-injectiveˡ ps≡1) leastDigs1) l≯128
  ... | yes l>128 =
    return (yes (success (lₚ' ∷ʳ lₑ) _ read≡ (mkOIDSub lₚ' lₚ≥128 lₑ (≰⇒> ¬lₑ≥128) l>128 refl) suffix refl))

open parseOIDSub public using (parseOIDSub)

module parseOIDField where
  here' = "parseOIDField"

  parseOIDValue : ∀ n → Parser (Logging ∘ Dec) (ExactLength OIDValue n)
  parseOIDValue n = parseBoundedSequenceOf "oid elems" OIDSub Sub.nonempty Sub.nosubstrings parseOIDSub n 1

  parseOID : Parser (Logging ∘ Dec) OID
  parseOID = parseTLV Tag.ObjectIdentifier "oid" _ parseOIDValue

open parseOIDField public using (parseOIDValue ; parseOID)

-- private
--   module Test where

--     open X509.SOID

--     test₁ : OID Md5Rsa
--     test₁ = Success.value (toWitness {Q = Logging.val (runParser parseOID Md5Rsa)} tt)

--     test₂ : OID Sha1Rsa
--     test₂ = Success.value (toWitness {Q = Logging.val (runParser parseOID Sha1Rsa)} tt)

--     test₃ : OID RsaPss
--     test₃ = Success.value (toWitness {Q = Logging.val (runParser parseOID RsaPss)} tt)

--     test₄ : OID Sha256Rsa
--     test₄ = Success.value (toWitness {Q = Logging.val (runParser parseOID Sha256Rsa)} tt)

--     test₅ : OID Sha384Rsa
--     test₅ = Success.value (toWitness {Q = Logging.val (runParser parseOID Sha384Rsa)} tt)

--     test₆ : OID Sha512Rsa
--     test₆ = Success.value (toWitness {Q = Logging.val (runParser parseOID Sha512Rsa)} tt)

--     test₇ : OID Sha224Rsa
--     test₇ = Success.value (toWitness {Q = Logging.val (runParser parseOID Sha224Rsa)} tt)

