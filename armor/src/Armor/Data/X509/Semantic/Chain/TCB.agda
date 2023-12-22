{-# OPTIONS  --sized-types #-}

open import Armor.Binary
open import Armor.Data.X509
open import Armor.Data.X509.Semantic.Chain.NameMatch
open import Armor.Prelude

module Armor.Data.X509.Semantic.Chain.TCB where

-- IssuerFor c₁ c₂ := "a cert for the issuer of c₁ is c₂"
_IsIssuerFor_ : ∀ {@0 bs₁ bs₂} → Cert bs₁ → Cert bs₂ → Set
_IsIssuerFor_ issuer issuee = NameMatch (Cert.getIssuer issuee) (Cert.getSubject issuer)

_isIssuerFor?_ :  ∀ {@0 bs₁ bs₂} → (issuer : Cert bs₁) → (issuee : Cert bs₂) → Dec (issuer IsIssuerFor issuee)
issuer isIssuerFor? issuee = nameMatch? (Cert.getIssuer issuee) (Cert.getSubject issuer)

_IsIssuerFor_In_ : ∀ {@0 bs₁ bs₂} → Cert bs₁ → Cert bs₂ → (certs : List (Exists─ _ Cert)) → Set
issuer IsIssuerFor issuee In certs = issuer IsIssuerFor issuee × (─ _ , issuer) ∈ certs

IssuerFor_In_ : ∀ {@0 bs} → Cert bs → List (Exists─ _ Cert) → Set
IssuerFor issuee In certs = Σ (Exists─ _ Cert) (λ where (─ _ , issuer) → issuer IsIssuerFor issuee In certs)

IssuersFor_In_ : {@0 bs : List UInt8} (issuee : Cert bs) (certs : List (Exists─ _ Cert)) → Set
IssuersFor issuee In certs = List (IssuerFor issuee In certs)

pattern anIssuerForIn{bs} issuer isIssuerFor issuer∈ = _,_ (_,_ (─_ bs) issuer) (_,_ isIssuerFor issuer∈)

getIssuerCert : ∀ {@0 bs} {issuee : Cert bs} {certs} → (iss : IssuerFor issuee In certs) → Cert (¡ proj₁ (proj₁ iss))
getIssuerCert (anIssuerForIn{bs} issuer _ _) = issuer

IsAllIssuersForIn-syntax : {@0 bs : List UInt8} (issuee : Cert bs) (certs : List (Exists─ _ Cert)) → IssuersFor issuee In certs → Set
IsAllIssuersForIn-syntax issuee certs issuers = All (λ (─ _ , cert) → cert IsIssuerFor issuee → (-, cert) ∈ map proj₁ issuers) certs

syntax IsAllIssuersForIn-syntax issuee certs issuers = issuers IsAllIssuersFor issuee In certs

AllIssuersFor_In_ : {@0 bs : List UInt8} (issuee : Cert bs) (certs : List (Exists─ _ Cert)) → Set
AllIssuersFor issuee In certs = Σ (IssuersFor issuee In certs) λ issuers → (issuers IsAllIssuersFor issuee In certs)


{- https://datatracker.ietf.org/doc/html/rfc5280#section-6.1
-- The trust anchor is an input to the algorithm.  There is no
-- requirement that the same trust anchor be used to validate all
-- certification paths.  Different trust anchors MAY be used to validate
-- different paths, as discussed further in Section 6.2.
--
-- The primary goal of path validation is to verify the binding between
-- a subject distinguished name or a subject alternative name and
-- subject public key, as represented in the target certificate, based
-- on the public key of the trust anchor.  In most cases, the target
-- certificate will be an end entity certificate, but the target
-- certificate may be a CA certificate as long as the subject public key
-- is to be used for a purpose other than verifying the signature on a
-- public key certificate.  Verifying the binding between the name and
-- subject public key requires obtaining a sequence of certificates that
-- support that binding.  The procedure performed to obtain this
-- sequence of certificates is outside the scope of this specification.
--
-- To meet this goal, the path validation process verifies, among other
-- things, that a prospective certification path (a sequence of n
-- certificates) satisfies the following conditions:
--
--    (a)  for all x in {1, ..., n-1}, the subject of certificate x is
--         the issuer of certificate x+1;
--
--    (b)  certificate 1 is issued by the trust anchor;
--
--    (c)  certificate n is the certificate to be validated (i.e., the
--         target certificate); and
--
--    (d)  for all x in {1, ..., n}, the certificate was valid at the
--         time in question.
--
-- A certificate MUST NOT appear more than once in a prospective
-- certification path.
--
-- When the trust anchor is provided in the form of a self-signed
-- certificate, this self-signed certificate is not included as part of
-- the prospective certification path.  Information about trust anchors
-- is provided as inputs to the certification path validation algorithm
-- (Section 6.1.1).
-}

abstract
  removeCertFromCerts : ∀ {@0 bs} → Cert bs → List (Exists─ _ Cert) → List (Exists─ _ Cert)
  removeCertFromCerts issuer certs = filter (λ c → _≠_ ⦃ TLV.eqTLV ⦃ Cert.eq ⦄ ⦄ c (-, issuer)) certs

  ∈removeCertFromCerts⇒
    : ∀ {@0 bs₁ bs₂} {c₁ : Cert bs₁} {c₂ : Cert bs₂} (certs : List (Exists─ _ Cert))
      → (-, c₁) ∈ removeCertFromCerts c₂ certs → (-, c₁) ∈ certs
  ∈removeCertFromCerts⇒{c₁ = c₁}{c₂} certs c₁∈ = proj₁ (∈.∈-filter⁻ (_≠ (-, c₂)) c₁∈)
    where
    import Data.List.Membership.Propositional.Properties as ∈

  ∉removeCertFromCerts : ∀ {@0 bs} (c : Cert bs) (certs : List (Exists─ _ Cert)) → (-, c) ∉ removeCertFromCerts c certs
  ∉removeCertFromCerts c certs c∈removed =
    contradiction refl (proj₂ (∈.∈-filter⁻ (_≠ (-, c)) {xs = certs} c∈removed))
    where
    import Data.List.Membership.Propositional.Properties as ∈

  removeCertFromCerts< : ∀ {@0 bs} (c : Cert bs) (certs : List (Exists─ _ Cert)) → (-, c) ∈ certs → length (removeCertFromCerts c certs) < length certs
  removeCertFromCerts< c certs c∈ = filter-notAll (_≠ (-, c)) certs (Any.map (λ where ≡c ≢c → ≢c (sym ≡c)) c∈)

data Chain (trustedRoot candidates : List (Exists─ _ Cert)) : ∀ {@0 bs} → Cert bs → Set where
  root : ∀ {@0 bs} {c : Cert bs} → IssuerFor c In trustedRoot → Chain trustedRoot candidates c
  link : ∀ {@0 bs₁ bs₂} (issuer : Cert bs₁) {c₂ : Cert bs₂}
         → (isIn : issuer IsIssuerFor c₂ In candidates)
         → Chain (removeCertFromCerts issuer trustedRoot)
                 (removeCertFromCerts issuer candidates)
                 issuer
         → Chain trustedRoot candidates c₂

isLink? : ∀ {trustedRoot candidates : List (Exists─ _ Cert)} {@0 bs} {c : Cert bs}
          → Chain trustedRoot candidates c → Bool
isLink? (root _) = false
isLink? (link _ _ _) = true

-- produces a list of certs corresponding to the chain, plus the trusted issuer certificate
toList : ∀ {trustedRoot candidates} {@0 bs} {issuee : Cert bs} → Chain trustedRoot candidates issuee → List (Exists─ _ Cert)
toList{issuee = issuee} (root (issuer , _)) = (-, issuee) ∷ [ issuer ]
toList{trustedRoot}{issuee = issuee} (link issuer isIn chain) = (-, issuee) ∷ toList chain

getPath : ∀ {trustedRoot candidates} {@0 bs} {issuee : Cert bs} → Chain trustedRoot candidates issuee → List (Exists─ _ Cert)
getPath c = take (length certs - 1) certs
  where
  certs = toList c

getIssuers : ∀ {trustedRoot candidates} {@0 bs} {issuee : Cert bs} → Chain trustedRoot candidates issuee → List (Exists─ _ Cert)
getIssuers c = drop 1 (toList c)

getIntermediates : ∀ {trustedRoot candidates} {@0 bs} {issuee : Cert bs} → Chain trustedRoot candidates issuee → List (Exists─ _ Cert)
getIntermediates c = take (length issuers - 1) issuers
  where
  issuers = getIssuers c

toListLength≥1 : ∀ {trustedRoot candidates} {@0 bs} {issuee : Cert bs} → (c : Chain trustedRoot candidates issuee)
                 → length (toList c) ≥ 1
toListLength≥1 (root _) = s≤s z≤n
toListLength≥1 (link _ _ c) = s≤s z≤n

-- certificates in chain are unique
ChainUnique : ∀ {trustedRoot candidates} {@0 bs} {issuee : Cert bs} → Chain trustedRoot candidates issuee → Set
ChainUnique c = List.Unique _≟_ (toList c)

-- chain equality (modulo proofs of "IsIssuerFor")
_≡Chain_ : {trustedRoot candidates : List (Exists─ _ Cert)} → ∀ {@0 bs} {endEnt : Cert bs} → (c₁ c₂ : Chain trustedRoot candidates endEnt) → Set
c₁ ≡Chain c₂ = toList c₁ ≡ toList c₂
-- data _≡Chain_ {trustedRoot candidates : List (Exists─ _ Cert)} : ∀ {@0 bs} {endEnt : Cert bs} → (c₁ c₂ : Chain trustedRoot candidates endEnt) → Set where
--   root : ∀ {@0 bs} {c : Cert bs} → (iss₁ iss₂ : IssuerFor c In trustedRoot)
--          → proj₁ iss₁ ≡ proj₁ iss₂
--          → (root{c = c} iss₁) ≡Chain (root{c = c} iss₂)
--   link : ∀ {@0 bs₁ bs₂} (issuer : Cert bs₁) {c : Cert bs₂}
--          → (isIssuer₁ isIssuer₂ : issuer IsIssuerFor c)
--          → (isIn₁ isIn₂ : (-, issuer) ∈ candidates)
--          → (c₁ c₂ : Chain (removeCertFromCerts issuer trustedRoot) (removeCertFromCerts issuer candidates) issuer) → c₁ ≡Chain c₂
--          → (link issuer {c} (isIssuer₁ , isIn₁) c₁) ≡Chain (link issuer {c} (isIssuer₂ , isIn₂) c₂)
