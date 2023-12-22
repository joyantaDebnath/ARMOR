{-# OPTIONS --sized-types #-}

open import Armor.Binary
open import Armor.Data.X509
open import Armor.Data.X509.Semantic.Cert.Utils
open import Armor.Data.X509.Semantic.Chain.NameMatch
import      Armor.Data.X509.Semantic.Chain.TCB as Chain
import      Armor.Grammar.Option
open import Armor.Prelude

module Armor.Data.X509.Semantic.Chain.R20 where

open Armor.Grammar.Option UInt8
open Chain using (Chain)

-- https://datatracker.ietf.org/doc/html/rfc5280#section-4.2.1.9
-- The PathLenConstraint field is meaningful only if the CA boolean
-- is asserted and the Key Usage extension, if present, asserts the KeyCertSign bit. In this case, it gives
-- the maximum number of non-self-issued intermediate certificates that may follow this certificate in a valid certification path.

countNextIntCACerts : List (Exists─ _ Cert) → ℤ → ℤ
countNextIntCACerts [] n = n
countNextIntCACerts ((_ , cert) ∷ certs) n =
  case Cert.isCA cert of λ where
    nothing → countNextIntCACerts certs n
    (just false) → countNextIntCACerts certs n
    (just true) → case nameMatch? (Cert.getIssuer cert) (Cert.getSubject cert) of λ where
      (no  _) → countNextIntCACerts certs (n ℤ.+ ℤ.+ 1)
      (yes _) → countNextIntCACerts certs n
--   with isCA (Cert.getBC snd)
-- ... | false = countNextIntCACerts x₁ n
-- ... | true
--   with nameMatch? (Cert.getIssuer snd) (Cert.getSubject snd)
-- ... | no ¬p =  countNextIntCACerts x₁ (n ℤ.+ ℤ.+ 1) 
-- ... | yes p =  countNextIntCACerts x₁ n

PathWithinMax : Exists─ _ Cert → List (Exists─ _ Cert) → Set
PathWithinMax (_ , cert) certs
  with ⌊ isConfirmedCA? cert ⌋ ∧ isKeyCertSignPresent (Cert.getKU cert)
... | false = ⊤
... | true
  with getBCPathLen (Cert.getBC cert)
... | (─ _ , none) = ⊤
... | (_ , some x) = countNextIntCACerts certs (ℤ.+ 0) ℤ.≤ Int.getVal x

--   with isCA (Cert.getBC snd) ∧ isKeyCertSignPresent (Cert.getKU snd)
-- ... | false = ⊤
-- ... | true
--   with (getBCPathLen (Cert.getBC snd))
-- ... | (─ .[] , none) = ⊤
-- ... | (fst , some x) = countNextIntCACerts x₁ (ℤ.+ 0) ℤ.≤ Int.getVal x

AllPathWithinMax : List (Exists─ _ Cert) → Set
AllPathWithinMax [] = ⊤
AllPathWithinMax (cert ∷ certs) =  PathWithinMax cert certs × AllPathWithinMax certs

pathWithinMax? : (c : Exists─ (List UInt8) Cert) → (t : List (Exists─ (List UInt8) Cert)) → Dec (PathWithinMax c t)
pathWithinMax? (_ , cert) certs
  with ⌊ isConfirmedCA? cert ⌋ ∧ isKeyCertSignPresent (Cert.getKU cert)
... | false = yes tt
... | true
  with getBCPathLen (Cert.getBC cert)
... | (─ .[] , none) = yes tt
... | (fst , some x) = countNextIntCACerts certs (ℤ.+ 0) ℤ.≤? Int.getVal x

module _ {trust candidates : List (Exists─ _ Cert)} {@0 bs} (issuee : Cert bs) where

  R20 :  Chain trust candidates issuee → Set
  R20 c = AllPathWithinMax (reverse (Chain.toList c))

  r20 : Decidable R20
  r20 c = allPathWithinMax? (reverse (Chain.toList c))
    where
    allPathWithinMax? : (c : List (Exists─ (List UInt8) Cert)) → Dec (AllPathWithinMax c)
    allPathWithinMax? [] = yes tt
    allPathWithinMax? (x ∷ x₁) = pathWithinMax? x x₁ ×-dec allPathWithinMax? x₁
