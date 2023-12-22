{-# OPTIONS  --sized-types #-}

open import Armor.Binary
open import Armor.Data.X509
open import Armor.Data.X509.Semantic.Chain.NameMatch
open import Armor.Data.X509.Semantic.Chain.Properties
open import Armor.Data.X509.Semantic.Chain.TCB
open import Armor.Prelude
import      Data.List as List
import      Data.List.Membership.Propositional as List
import      Data.List.Membership.Propositional.Properties as List

module Armor.Data.X509.Semantic.Chain.Builder where

-- data TrustTree (trustedRoot candidates : List (Exists─ _ Cert)) : ∀ {@0 bs} → Cert bs → Set
TrustTreeBranchF : ∀ {@0 bs} trustedRoot candidates (issuee : Cert bs) → IssuerFor issuee In candidates → Set
record TrustTree (trustedRoot candidates : List (Exists─ _ Cert)) {@0 bs : List UInt8} (issuee : Cert bs) : Set

-- data TrustTree trustedRoot candidates where
--   trustTree : ∀ {@0 bs} → (issuee : Cert bs) → TrustTreeNode trustedRoot candidates issuee → TrustTree trustedRoot candidates issuee

TrustTreeBranchF trustedRoot candidates issuee (anIssuerForIn issuer isIssuerFor issuer∈) =
  TrustTree (removeCertFromCerts issuer trustedRoot) (removeCertFromCerts issuer candidates) issuer

record TrustTree trustedRoot candidates {bs} issuee where
  inductive
  constructor mkTrustTree
  field
    rootIssuers  : AllIssuersFor issuee In trustedRoot
    otherIssuers : AllIssuersFor issuee In candidates
    otherTrust   : All (TrustTreeBranchF trustedRoot candidates issuee) (proj₁ otherIssuers)

findIssuersFor : ∀ {@0 bs} → (issuee : Cert bs) → (certs : List (Exists─ _ Cert)) → AllIssuersFor issuee In certs
findIssuersFor issuee [] = [] , []
findIssuersFor issuee ((─ _ , cert) ∷ certs) =
  case cert isIssuerFor? issuee of λ where
    (yes isIssuer) →
      Product.map (λ issuers → ((-, cert) , (isIssuer , (here refl))) ∷ weaken issuers)
      (λ {issuers} isAllIssuersForIn →
        All.tabulate (λ where
          {─ _ , cert} (here px) isIssuerFor → here px
          {─ _ , cert} (there cert∈) isIssuerFor →
            there (∈weaken issuers (-, cert) (All.lookup isAllIssuersForIn cert∈ isIssuerFor))))
      issuers
    (no ¬isIssuer) →
      Product.map
        (λ issuers → weaken issuers)
        (λ {issuers} isAllIssuersForIn →
          All.tabulate λ where
            {─ _ , cert} (here refl) isIssuerFor →
              contradiction isIssuerFor ¬isIssuer
            {─ _ , cert} (there c∈) isIssuerFor →
              ∈weaken issuers (-, cert) (All.lookup isAllIssuersForIn c∈ isIssuerFor))
        issuers
  where
  import Data.Product as Product

  issuers : AllIssuersFor issuee In certs
  issuers = findIssuersFor issuee certs

  weaken₁ : IssuerFor issuee In certs → IssuerFor issuee In ((-, cert) ∷ certs)
  weaken₁ = (λ where (anIssuerForIn issuer isIssuerFor issuer∈) → anIssuerForIn issuer isIssuerFor (there issuer∈))

  weaken : IssuersFor issuee In certs → IssuersFor issuee In ((-, cert) ∷ certs)
  weaken issuers = map weaken₁ issuers

  ∈weaken : (issuers : IssuersFor issuee In certs) → (c : Exists─ _ Cert) → c ∈ map proj₁ issuers → c ∈ map proj₁ (weaken issuers)
  ∈weaken issuers (─ _ , c) c∈issuers = subst (_∈ map proj₁ (weaken issuers)) c≡ c∈
    where
    lem : ∃ λ x → x ∈ issuers × (-, c) ≡ proj₁ x
    lem = List.∈-map⁻ proj₁ c∈issuers

    c∈ : proj₁ (weaken₁ (proj₁ lem)) ∈ map proj₁ (weaken issuers)
    c∈ = List.∈-map⁺ proj₁ (List.∈-map⁺ weaken₁ (proj₁ (proj₂ lem)))

    c≡ : proj₁ (weaken₁ (proj₁ lem)) ≡ (-, c)
    c≡ = case lem ret (λ x → proj₁ (weaken₁ (proj₁ x)) ≡ (-, c)) of λ where
      (anIssuerForIn _ _ _ , (_ , refl)) → refl

buildTrustTreeWF : (trustedRoot candidates : List (Exists─ _ Cert)) → @0 Acc _<_ (length candidates)
               → ∀ {@0 bs} → (issuee : Cert bs) → TrustTree trustedRoot candidates issuee
buildTrustTreeWF trustedRoot candidates (WellFounded.acc rs) {bs} issuee =
  mkTrustTree rootIssuers otherIssuers (All.tabulate ih)
--   mkTrustTree rootIssuers otherIssuers (All.tabulate ih)
  where
  rootIssuers : AllIssuersFor issuee In trustedRoot
  rootIssuers = findIssuersFor issuee trustedRoot

  otherIssuers : AllIssuersFor issuee In candidates
  otherIssuers = findIssuersFor issuee candidates

  ih : {iss : IssuerFor issuee In candidates} → iss ∈ proj₁ otherIssuers
       → TrustTreeBranchF trustedRoot candidates issuee iss
  ih{anIssuerForIn issuer isIssuerFor issuer∈candidates} ∈otherIssuers =
    buildTrustTreeWF (removeCertFromCerts issuer trustedRoot) (removeCertFromCerts issuer candidates)
      (rs _ (removeCertFromCerts< issuer candidates issuer∈candidates))
      issuer

buildTrustTree : (trustedRoot candidates : List (Exists─ _ Cert))
                 → ∀ {@0 bs} → (issuee : Cert bs) → TrustTree trustedRoot candidates issuee
buildTrustTree trustedRoot candidates = buildTrustTreeWF trustedRoot candidates (<-wellFounded _)
  where
  open import Data.Nat.Induction

toChainsBranchWF
  : ∀ (trustedRoot candidates : List (Exists─ _ Cert)) {@0 bs} (endEnt : Cert bs)
    → @0 Acc _<_ (length candidates)
    → ∃ (TrustTreeBranchF trustedRoot candidates endEnt) → List (Chain trustedRoot candidates endEnt)

toChainsWF : ∀ (trustedRoot candidates : List (Exists─ _ Cert)) {@0 bs} (endEnt : Cert bs)
             → @0 Acc _<_ (length candidates)
             → TrustTree trustedRoot candidates endEnt
             → List (Chain trustedRoot candidates endEnt)

toChainsBranchWF trustedRoot candidates endEnt (WellFounded.acc rs) (anIssuerForIn issuer isIssuerFor issuer∈ , tr) =
  map (link issuer (isIssuerFor , issuer∈))
    (toChainsWF (removeCertFromCerts issuer trustedRoot) (removeCertFromCerts issuer candidates)
      issuer
      (rs _ (removeCertFromCerts< issuer candidates issuer∈))
      tr)

toChainsWF trustedRoot candidates endEnt ac (mkTrustTree rootIssuers otherIssuers otherTrust) =
     map root (proj₁ rootIssuers)
  ++ concatMap (toChainsBranchWF trustedRoot candidates endEnt ac) (All.toList otherTrust)

toChains : ∀ (trustedRoot candidates : List (Exists─ _ Cert)) {@0 bs} (endEnt : Cert bs)
           → TrustTree trustedRoot candidates endEnt
           → List (Chain trustedRoot candidates endEnt)
toChains trustedRoot candidates endEnt tr = toChainsWF trustedRoot candidates endEnt (<-wellFounded _) tr
  where
  open import Data.Nat.Induction

buildChains : (trustedRoot candidates : List (Exists─ _ Cert))
              → ∀ {@0 bs} → (issuee : Cert bs)
              → List (Chain trustedRoot candidates issuee)
buildChains trustedRoot candidates issuee =
  toChains _ _ _ (buildTrustTree trustedRoot candidates issuee)

-- completeness

toChainsBranchCompleteWF
  : ∀ (trustedRoot candidates : List (Exists─ _ Cert))
    → ∀ {@0 bs} (issuee : Cert bs)
    → (@0 ac : Acc _<_ (length candidates))
    → (tb : ∃ (TrustTreeBranchF trustedRoot candidates issuee))
    → let (anIssuerForIn issuer _ issuer∈) = proj₁ tb in
      ∀ (isIssuerFor : issuer IsIssuerFor issuee) (issuer∈' : (-, issuer) ∈ candidates)
      → (chain : Chain (removeCertFromCerts issuer trustedRoot) (removeCertFromCerts issuer candidates) issuer)
      → Any{A = Chain trustedRoot candidates issuee} (λ c → link issuer (isIssuerFor , issuer∈') chain ≡Chain c) (toChainsBranchWF _ _ _ ac tb)


toChainsCompleteWF
  : ∀ (trustedRoot candidates : List (Exists─ _ Cert))
    → ∀ {@0 bs} (issuee : Cert bs)
    → (@0 ac : Acc _<_ (length candidates))
    → (tr : TrustTree trustedRoot candidates issuee)
    → (c : Chain trustedRoot candidates issuee)
    → Any (c ≡Chain_) (toChainsWF _ _ _ ac tr)

toChainsBranchCompleteWF trustedRoot candidates {- unique -} issuee (WellFounded.acc rs) ((anIssuerForIn issuer isIssuerFor issuer∈) , tr) isIssuerFor' issuer∈' chain =
  Any.map⁺{xs = chains'}
    (Any.map
      (λ {chain'} ≡chain → cong₂ _∷_ refl ≡chain)
      ih)
  where
  chains' : List (Chain (removeCertFromCerts issuer trustedRoot) (removeCertFromCerts issuer candidates) issuer)
  chains' = toChainsWF _ _ issuer (rs _ (removeCertFromCerts< _ candidates issuer∈)) tr

  ih : Any (chain ≡Chain_) chains'
  ih = toChainsCompleteWF _ _ issuer (rs _ (removeCertFromCerts< _ candidates issuer∈)) tr chain

allLookupLemma : {A : Set} {P : (a : A) → Set} → ∀ {x xs} → (all : All P xs) → (x∈ : x ∈ xs) → ((x , All.lookup all x∈)) ∈ All.toList all
allLookupLemma {x} {xs} (px₁ ∷ all₁) (here refl) = here refl
allLookupLemma {x} {xs} (px ∷ all₁) (there x∈) = there (allLookupLemma all₁ x∈)


toChainsCompleteWF trustedRoot candidates {- unique -} endEnt ac (mkTrustTree (rootIssuers , allRootIssuers) otherIssuers otherTrust) (root (anIssuerForIn issuer isIssuerFor issuer∈)) =
  Any.++⁺ˡ {xs = map root rootIssuers}
    (Any.map⁺
      (List.lose rootIssuer∈root (cong₂ (λ x y → x ∷ [ y ]) refl (proj₂ (proj₂ rootIssuerLem)))))
  where
  rootIssuerLem : ∃ λ x → x ∈ rootIssuers × (-, issuer) ≡ proj₁ x
  rootIssuerLem = List.∈-map⁻ proj₁ (All.lookup allRootIssuers issuer∈ isIssuerFor)

  rootIssuer = proj₁ rootIssuerLem
  rootIssuer∈root = proj₁ (proj₂ rootIssuerLem)
toChainsCompleteWF trustedRoot candidates {- unique -} endEnt ac (mkTrustTree (rootIssuers , _) (otherIssuers , allOtherIssuers) otherTrust) chain@(link issuer (isIssuer , issuer∈) c) =
  Any.++⁺ʳ (map root rootIssuers)
    (Any.concat⁺{xss = map (toChainsBranchWF trustedRoot candidates endEnt ac) (All.toList otherTrust)}
      (Any.map⁺{xs = All.toList otherTrust}
        (List.lose
          (allLookupLemma otherTrust (proj₂ (isIssuer×isInF issuerFromOtherIssuers)))
          (toChainsBranchCompleteWF trustedRoot candidates endEnt ac
            (  (  (-, issuer)
                , proj₁ (proj₁ (isIssuer×isInF issuerFromOtherIssuers))
                , proj₂ (proj₁ (isIssuer×isInF issuerFromOtherIssuers)))
             , All.lookup otherTrust _)
            isIssuer issuer∈
            c))))
  where
  xs = concatMap (toChainsBranchWF trustedRoot candidates endEnt ac) (All.toList otherTrust)

  issuerFromOtherIssuers : ∃ λ x → x ∈ otherIssuers × (-, issuer) ≡ proj₁ x
  issuerFromOtherIssuers = List.∈-map⁻ proj₁ (All.lookup allOtherIssuers issuer∈ isIssuer)

  isIssuer×isInF : (∃ λ x → x ∈ otherIssuers × (-, issuer) ≡ proj₁ x)
                   → Σ (issuer IsIssuerFor endEnt In candidates) λ isIssIn → ((-, issuer) , isIssIn) ∈ otherIssuers
  isIssuer×isInF ((_ , ret) , x∈otherIssuers , refl) = ret , x∈otherIssuers

toChainsComplete
  : ∀ (trustedRoot candidates : List (Exists─ _ Cert))
    → ∀ {@0 bs} (issuee : Cert bs)
    → (tr : TrustTree trustedRoot candidates issuee)
    → (c : Chain trustedRoot candidates issuee)
    → Any (c ≡Chain_) (toChains _ _ _ tr)
toChainsComplete trust candidates issuee =
  toChainsCompleteWF trust candidates issuee (<-wellFounded _)
  where
  open import Data.Nat.Induction

buildChainsComplete : ∀ trust candidates {@0 bs} (issuee : Cert bs) → (c : Chain trust candidates issuee)
                      → Any (c ≡Chain_) (buildChains trust candidates issuee)
buildChainsComplete trust candidates issuee =
  toChainsComplete trust candidates issuee (buildTrustTree trust candidates issuee)
