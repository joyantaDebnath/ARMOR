open import Armor.Binary
open import Armor.Data.X509.Extension.AIA.TCB
open import Armor.Data.X509.Extension.AKI.TCB
open import Armor.Data.X509.Extension.BC.TCB
open import Armor.Data.X509.Extension.CRLDistPoint.TCB
open import Armor.Data.X509.Extension.CertPolicy.TCB
open import Armor.Data.X509.Extension.EKU.TCB
open import Armor.Data.X509.Extension.IAN.TCB
open import Armor.Data.X509.Extension.INAP.TCB
open import Armor.Data.X509.Extension.KU.TCB
open import Armor.Data.X509.Extension.NC.TCB
open import Armor.Data.X509.Extension.PC.TCB
open import Armor.Data.X509.Extension.PM.TCB
open import Armor.Data.X509.Extension.SAN.TCB
open import Armor.Data.X509.Extension.SKI.TCB
import      Armor.Data.X509.Extension.TCB.OIDs as OIDs
open import Armor.Data.X690-DER.Boool.TCB
open import Armor.Data.X690-DER.Boool.Eq
open import Armor.Data.X690-DER.Default.TCB
open import Armor.Data.X690-DER.OID.TCB
open import Armor.Data.X690-DER.OctetString.TCB
open import Armor.Data.X690-DER.TLV.TCB
open import Armor.Data.X690-DER.TLV.Properties
open import Armor.Data.X690-DER.SequenceOf.TCB
open import Armor.Data.X690-DER.Length.TCB
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Definitions
import      Armor.Grammar.IList.TCB
import      Armor.Grammar.Option.TCB
import      Armor.Grammar.Parallel.TCB
import      Armor.Grammar.Sum.TCB
import      Armor.Grammar.Seq
open import Armor.Prelude

module Armor.Data.X509.Extension.TCB where

open Armor.Grammar.Definitions  UInt8
open Armor.Grammar.IList.TCB    UInt8
open Armor.Grammar.Option.TCB   UInt8
open Armor.Grammar.Parallel.TCB UInt8
open Armor.Grammar.Sum.TCB      UInt8
open Armor.Grammar.Seq         UInt8

-- https://datatracker.ietf.org/doc/html/rfc5280#section-4.1
--    Extensions  ::=  SEQUENCE SIZE (1..MAX) OF Extension

--    Extension  ::=  SEQUENCE  {
--         extnID      OBJECT IDENTIFIER,
--         critical    BOOLEAN DEFAULT FALSE,
--         extnValue   OCTET STRING
--                     -- contains the DER encoding of an ASN.1 value
--                     -- corresponding to the extension type identified
--                     -- by extnID
--         }

supportedExtensions : List (List UInt8)
supportedExtensions =
    OIDs.AKILit ∷ OIDs.SKILit ∷ OIDs.KULit ∷ OIDs.EKULit ∷ OIDs.BCLit ∷ OIDs.IANLit ∷ OIDs.SANLit
  ∷ OIDs.CPOLLit ∷ OIDs.CRLDISTLit ∷ OIDs.NCLit ∷ OIDs.PCLit ∷ OIDs.PMLit ∷ OIDs.INAPLit ∷ [ OIDs.AIALit ]

record ExtensionFields (@0 P : List UInt8 → Set) (A : @0 List UInt8 → Set) (@0 bs : List UInt8) : Set where
  constructor mkExtensionFields
  field
    @0 {oex cex ocex} : List UInt8
    extnId : OID oex
    @0 extnId≡ : P (TLV.v extnId) -- oex ≡ lit
    crit : Default Boool falseBoool cex
    extension : A ocex
    @0 bs≡ : bs ≡ oex ++ cex ++ ocex

ExtensionFieldAIA     = ExtensionFields (_≡ OIDs.AIALit )    AIAFields
ExtensionFieldAKI     = ExtensionFields (_≡ OIDs.AKILit )    AKIFields
ExtensionFieldBC      = ExtensionFields (_≡ OIDs.BCLit  )    BCFields
ExtensionFieldCPOL    = ExtensionFields (_≡ OIDs.CPOLLit)    CertPolFields
ExtensionFieldCRLDist = ExtensionFields (_≡ OIDs.CRLDISTLit) CRLDistFields
ExtensionFieldEKU     = ExtensionFields (_≡ OIDs.EKULit )    EKUFields
ExtensionFieldIAN     = ExtensionFields (_≡ OIDs.IANLit )    IANFields     
ExtensionFieldINAP    = ExtensionFields (_≡ OIDs.INAPLit)    INAPFields
ExtensionFieldKU      = ExtensionFields (_≡ OIDs.KULit  )    KUFields
ExtensionFieldNC      = ExtensionFields (_≡ OIDs.NCLit  )    NCFields
ExtensionFieldPC      = ExtensionFields (_≡ OIDs.PCLit  )    PCFields
ExtensionFieldPM      = ExtensionFields (_≡ OIDs.PMLit  )    PMFields
ExtensionFieldSAN     = ExtensionFields (_≡ OIDs.SANLit )    SANFields
ExtensionFieldSKI     = ExtensionFields (_≡ OIDs.SKILit )    SKIFields

ExtensionFieldUnsupported = ExtensionFields (False ∘ (_∈? supportedExtensions)) OctetString

data SelectExtn : @0 List UInt8 → Set where
  akiextn  : ∀ {@0 bs} → ExtensionFieldAKI bs → SelectExtn bs 
  skiextn  : ∀ {@0 bs} → ExtensionFieldSKI bs → SelectExtn bs 
  kuextn   : ∀ {@0 bs} → ExtensionFieldKU bs  → SelectExtn bs 
  ekuextn  : ∀ {@0 bs} → ExtensionFieldEKU bs → SelectExtn bs 
  bcextn   : ∀ {@0 bs} → ExtensionFieldBC bs  → SelectExtn bs 
  ianextn  : ∀ {@0 bs} → ExtensionFieldIAN bs → SelectExtn bs 
  sanextn  : ∀ {@0 bs} → ExtensionFieldSAN bs → SelectExtn bs 
  cpextn   : ∀ {@0 bs} → ExtensionFieldCPOL bs → SelectExtn bs 
  crlextn  : ∀ {@0 bs} → ExtensionFieldCRLDist bs → SelectExtn bs 
  ncextn   : ∀ {@0 bs} → ExtensionFieldNC bs  → SelectExtn bs 
  pcextn   : ∀ {@0 bs} → ExtensionFieldPC bs → SelectExtn bs 
  pmextn   : ∀ {@0 bs} → ExtensionFieldPM bs → SelectExtn bs 
  inapextn : ∀ {@0 bs} → ExtensionFieldINAP bs → SelectExtn bs 
  aiaextn  : ∀ {@0 bs} → ExtensionFieldAIA bs → SelectExtn bs
  other    : ∀ {@0 bs} → ExtensionFieldUnsupported bs → SelectExtn bs

Extension : @0 List UInt8 → Set
Extension xs = TLV Tag.Sequence SelectExtn xs

ExtensionsSeq : @0 List UInt8 → Set
ExtensionsSeq xs = TLV Tag.Sequence (NonEmptySequenceOf Extension) xs

Extensions : @0 List UInt8 → Set
Extensions xs = TLV Tag.AA3  ExtensionsSeq xs

ExtensionFieldsRep : (@0 P : List UInt8 → Set) (A : @0 List UInt8 → Set) → @0 List UInt8 → Set
ExtensionFieldsRep P A = &ₚ (Σₚ OID (λ _ x → Erased (P (TLV.v x)))) (&ₚ (Default Boool falseBoool) A)

equivalentExtensionFields : ∀ {@0 P : List UInt8 → Set} {A : @0 List UInt8 → Set}
               → Equivalent (ExtensionFieldsRep P A) (ExtensionFields P A)
proj₁ equivalentExtensionFields (mk&ₚ (mk×ₚ fstₚ₁ (─ sndₚ₁)) (mk&ₚ fstₚ₂ sndₚ₂ refl) refl) =
    mkExtensionFields fstₚ₁ sndₚ₁ fstₚ₂ sndₚ₂ refl
proj₂ equivalentExtensionFields (mkExtensionFields extnId extnId≡ crit extension refl) =
    mk&ₚ (mk×ₚ extnId (─ extnId≡)) (mk&ₚ crit extension refl) refl

RawExtensionFieldsRep : ∀ {@0 P} {A : @0 List UInt8 → Set} (ra : Raw A) → Raw (ExtensionFieldsRep P A)
RawExtensionFieldsRep{P} ra = Raw&ₚ (RawΣₚ₁ RawOID (λ _ x → Erased (P (TLV.v x))))
                            (Raw&ₚ (RawDefault RawBoool falseBoool) ra)

RawExtensionFields : ∀ {@0 P} {A : @0 List UInt8 → Set} (ra : Raw A) → Raw (ExtensionFields P A)
RawExtensionFields ra = Iso.raw equivalentExtensionFields (RawExtensionFieldsRep ra)

SelectExtnRep = (Sum ExtensionFieldAKI
        (Sum ExtensionFieldSKI
        (Sum ExtensionFieldKU
        (Sum ExtensionFieldEKU
        (Sum ExtensionFieldBC
        (Sum ExtensionFieldIAN
        (Sum ExtensionFieldSAN
        (Sum ExtensionFieldCPOL
        (Sum ExtensionFieldCRLDist
        (Sum ExtensionFieldNC
        (Sum ExtensionFieldPC
        (Sum ExtensionFieldPM
        (Sum ExtensionFieldINAP
        (Sum ExtensionFieldAIA
             ExtensionFieldUnsupported))))))))))))))

equivalent : Equivalent SelectExtnRep SelectExtn
proj₁ equivalent (Sum.inj₁ x) = akiextn x
proj₁ equivalent (Sum.inj₂ (Sum.inj₁ x)) = skiextn x
proj₁ equivalent (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x))) = kuextn x
proj₁ equivalent (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x)))) = ekuextn x
proj₁ equivalent (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x))))) = bcextn x
proj₁ equivalent (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x)))))) = ianextn x
proj₁ equivalent (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x))))))) = sanextn x
proj₁ equivalent (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x)))))))) = cpextn x
proj₁ equivalent (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x))))))))) = crlextn x
proj₁ equivalent (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x)))))))))) = ncextn x
proj₁ equivalent (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x))))))))))) = pcextn x
proj₁ equivalent (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x)))))))))))) = pmextn x
proj₁ equivalent (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x))))))))))))) = inapextn x
proj₁ equivalent (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x)))))))))))))) = aiaextn x
proj₁ equivalent (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ x)))))))))))))) = other x
proj₂ equivalent (akiextn x) = Sum.inj₁ x
proj₂ equivalent (skiextn x) = Sum.inj₂ (Sum.inj₁ x)
proj₂ equivalent (kuextn x) = Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x))
proj₂ equivalent (ekuextn x)   = Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x)))
proj₂ equivalent (bcextn x)    = Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x))))
proj₂ equivalent (ianextn x)   = Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x)))))
proj₂ equivalent (sanextn x)   = Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x))))))
proj₂ equivalent (cpextn x)    = Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x)))))))
proj₂ equivalent (crlextn x)   = Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x))))))))
proj₂ equivalent (ncextn x)    = Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x)))))))))
proj₂ equivalent (pcextn x)    = Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x))))))))))
proj₂ equivalent (pmextn x)    = Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x)))))))))))
proj₂ equivalent (inapextn x)  = Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x))))))))))))
proj₂ equivalent (aiaextn x)   = Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x)))))))))))))
proj₂ equivalent (other x)     = Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ x)))))))))))))

RawSelectExtnRep : Raw SelectExtnRep
RawSelectExtnRep = RawSum (RawExtensionFields RawAKIFields)
                   (RawSum (RawExtensionFields RawSKIFields)
                   (RawSum (RawExtensionFields RawKUFields)
                   (RawSum (RawExtensionFields RawEKUFields)
                   (RawSum (RawExtensionFields RawBCFields)
                   (RawSum (RawExtensionFields RawIANFields)
                   (RawSum (RawExtensionFields RawSANFields)
                   (RawSum (RawExtensionFields RawCertPolFields)
                   (RawSum (RawExtensionFields RawCRLDistFields)
                   (RawSum (RawExtensionFields RawNCFields)
                   (RawSum (RawExtensionFields RawPCFields)
                   (RawSum (RawExtensionFields RawPMFields)
                   (RawSum (RawExtensionFields RawINAPFields)
                   (RawSum (RawExtensionFields RawAIAFields)
                           (RawExtensionFields RawOctetString))))))))))))))

RawSelectExtn : Raw SelectExtn
RawSelectExtn = Iso.raw equivalent RawSelectExtnRep

RawExtensions : Raw Extensions
RawExtensions = RawTLV _ (RawTLV _ (RawBoundedSequenceOf (RawTLV _ RawSelectExtn) 1))

module Extension where
  getBC : ∀ {@0 bs} → Extension bs → Exists─ (List UInt8) (Option ExtensionFieldBC)
  getBC (mkTLV len (bcextn x) len≡ bs≡) = _ , (some x)
  getBC (mkTLV len _ len≡ bs≡) = _ , none

  getKU : ∀ {@0 bs} → Extension bs → Exists─ (List UInt8) (Option ExtensionFieldKU)
  getKU (mkTLV len (kuextn x) len≡ bs≡) = _ , (some x)
  getKU (mkTLV len _ len≡ bs≡) = _ , none

  getEKU : ∀ {@0 bs} → Extension bs → Exists─ (List UInt8) (Option ExtensionFieldEKU)
  getEKU (mkTLV len (ekuextn x) len≡ bs≡) = _ , (some x)
  getEKU (mkTLV len _ len≡ bs≡) = _ , none

  getSAN : ∀ {@0 bs} → Extension bs → Exists─ (List UInt8) (Option ExtensionFieldSAN)
  getSAN (mkTLV len (sanextn x) len≡ bs≡) = _ , (some x)
  getSAN (mkTLV len _ len≡ bs≡) = _ , none

  getCRLDIST : ∀ {@0 bs} → Extension bs → Exists─ (List UInt8) (Option ExtensionFieldCRLDist)
  getCRLDIST (mkTLV len (crlextn x) len≡ bs≡) = _ , (some x)
  getCRLDIST (mkTLV len _ len≡ bs≡) = _ , none

  getCPOL : ∀ {@0 bs} → Extension bs → Exists─ (List UInt8) (Option ExtensionFieldCPOL)
  getCPOL (mkTLV len (cpextn x) len≡ bs≡) = _ , (some x)
  getCPOL (mkTLV len _ len≡ bs≡) = _ , none

module ExtensionsSeq where
  getBC : ∀ {@0 bs} → ExtensionsSeq bs → Exists─ (List UInt8) (Option ExtensionFieldBC)
  getBC (mkTLV len (mk×ₚ x sndₚ₁) len≡ bs≡) = helper x
    where
    helper : ∀ {@0 bs} → SequenceOf Extension bs → Exists─ (List UInt8) (Option ExtensionFieldBC)
    helper nil = _ , none
    helper (consIList h t bs≡) = case (Extension.getBC h) of λ where
      (─ .[] , none) → helper t
      y@(fst , some x) → y

  getKU : ∀ {@0 bs} → ExtensionsSeq bs → Exists─ (List UInt8) (Option ExtensionFieldKU)
  getKU (mkTLV len (mk×ₚ x sndₚ₁) len≡ bs≡) = helper x
    where
    helper : ∀ {@0 bs} → SequenceOf Extension bs → Exists─ (List UInt8) (Option _)
    helper nil = _ , none
    helper (consIList h t bs≡) = case (Extension.getKU h) of λ where
      (─ .[] , none) → helper t
      y@(fst , some x) → y

  getEKU : ∀ {@0 bs} → ExtensionsSeq bs → Exists─ (List UInt8) (Option ExtensionFieldEKU)
  getEKU (mkTLV len (mk×ₚ x sndₚ₁) len≡ bs≡) = helper x
    where
    helper : ∀ {@0 bs} → SequenceOf Extension bs → Exists─ (List UInt8) (Option _)
    helper nil = _ , none
    helper (consIList h t bs≡) = case (Extension.getEKU h) of λ where
      (─ .[] , none) → helper t
      y@(fst , some x) → y

  getSAN : ∀ {@0 bs} → ExtensionsSeq bs → Exists─ (List UInt8) (Option ExtensionFieldSAN)
  getSAN (mkTLV len (mk×ₚ x sndₚ₁) len≡ bs≡) = helper x
    where
    helper : ∀ {@0 bs} → SequenceOf Extension bs → Exists─ (List UInt8) (Option _)
    helper nil = _ , none
    helper (consIList h t bs≡) = case (Extension.getSAN h) of λ where
      (─ .[] , none) → helper t
      y@(fst , some x) → y

  getCRLDIST : ∀ {@0 bs} → ExtensionsSeq bs → Exists─ (List UInt8) (Option ExtensionFieldCRLDist)
  getCRLDIST (mkTLV len (mk×ₚ x sndₚ₁) len≡ bs≡) = helper x
    where
    helper : ∀ {@0 bs} → SequenceOf Extension bs → Exists─ (List UInt8) (Option _)
    helper nil = _ , none
    helper (consIList h t bs≡) = case (Extension.getCRLDIST h) of λ where
      (─ .[] , none) → helper t
      y@(fst , some x) → y

  getCPOL : ∀ {@0 bs} → ExtensionsSeq bs → Exists─ (List UInt8) (Option ExtensionFieldCPOL)
  getCPOL (mkTLV len (mk×ₚ x sndₚ₁) len≡ bs≡) = helper x
    where
    helper : ∀ {@0 bs} → SequenceOf Extension bs → Exists─ (List UInt8) (Option _)
    helper nil = _ , none
    helper (consIList h t bs≡) = case (Extension.getCPOL h) of λ where
      (─ .[] , none) → helper t
      y@(fst , some x) → y

  getExtensionsList : ∀ {@0 bs} → ExtensionsSeq bs → List (Exists─ (List UInt8) Extension)
  getExtensionsList (mkTLV len (mk×ₚ fstₚ₁ sndₚ₁) len≡ bs≡) = helper fstₚ₁
    where
    helper : ∀ {@0 bs} → SequenceOf Extension bs → List (Exists─ (List UInt8) Extension)
    helper nil = []
    helper (consIList h t bs≡) = (_ , h) ∷ helper t

module Extensions where
  getBC : ∀ {@0 bs} → Extensions bs → Exists─ (List UInt8) (Option ExtensionFieldBC)
  getBC (mkTLV len val len≡ bs≡) = ExtensionsSeq.getBC val

  getKU : ∀ {@0 bs} → Extensions bs → Exists─ (List UInt8) (Option ExtensionFieldKU)
  getKU (mkTLV len val len≡ bs≡) = ExtensionsSeq.getKU val

  getEKU : ∀ {@0 bs} → Extensions bs → Exists─ (List UInt8) (Option ExtensionFieldEKU)
  getEKU (mkTLV len val len≡ bs≡) = ExtensionsSeq.getEKU val

  getSAN : ∀ {@0 bs} → Extensions bs → Exists─ (List UInt8) (Option ExtensionFieldSAN)
  getSAN (mkTLV len val len≡ bs≡) = ExtensionsSeq.getSAN val

  getCRLDIST : ∀ {@0 bs} → Extensions bs → Exists─ (List UInt8) (Option ExtensionFieldCRLDist)
  getCRLDIST (mkTLV len val len≡ bs≡) = ExtensionsSeq.getCRLDIST val

  getCPOL : ∀ {@0 bs} → Extensions bs → Exists─ (List UInt8) (Option ExtensionFieldCPOL)
  getCPOL (mkTLV len val len≡ bs≡) = ExtensionsSeq.getCPOL val

  getExtensionsList : ∀ {@0 bs} → Extensions bs → List (Exists─ (List UInt8) Extension)
  getExtensionsList (mkTLV len val len≡ bs≡) = ExtensionsSeq.getExtensionsList val
