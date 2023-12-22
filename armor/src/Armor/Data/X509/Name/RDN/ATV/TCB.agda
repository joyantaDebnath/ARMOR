open import Armor.Binary
open import Armor.Data.X509.DirectoryString.TCB
open import Armor.Data.X690-DER.OID.Properties
open import Armor.Data.X690-DER.OID.TCB
open import Armor.Data.X509.Name.RDN.ATV.OIDs
open import Armor.Data.X690-DER.Sequence.DefinedByOID.TCB
open import Armor.Data.X690-DER.Strings.IA5String.TCB
open import Armor.Data.X690-DER.Strings.PrintableString.TCB
  renaming (size to sizePrintableString)
open import Armor.Data.X690-DER.TLV.TCB
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Definitions
import      Armor.Grammar.Parallel
open import Armor.Prelude

module Armor.Data.X509.Name.RDN.ATV.TCB where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Parallel    UInt8

-- https://datatracker.ietf.org/doc/html/rfc5280#appendix-A.1
-- AttributeType           ::= OBJECT IDENTIFIER
--
-- AttributeValue          ::= ANY -- DEFINED BY AttributeType
--
-- AttributeTypeAndValue   ::= SEQUENCE {
--         type    AttributeType,
--         value   AttributeValue }

pattern atvParamUnsupported{¬p}      = no ¬p
pattern atvParamX520DNQualifier{px}  = yes (here px)
pattern atvParamX520CountryName{px}  = yes (there (here px))
pattern atvParamX520SerialNumber{px} = yes (there (there (here px)))
pattern atvParamPCKS9Email{px}       = yes (there (there (there (here px))))
pattern atvParamDomainComponent{px}  = yes (there (there (there (there (here px)))))

ATVParam : {@0 bs : List UInt8} → (o : OID bs) → Dec ((-, TLV.val o) ∈ Supported) → @0 List UInt8 → Set
-- Default
ATVParam o atvParamUnsupported = DirectoryString
-- X520 DN Qualifier
ATVParam o atvParamX520DNQualifier = PrintableString
-- X520 Country Name
ATVParam o atvParamX520CountryName = Σₚ PrintableString (TLVSizeBounded sizePrintableString 2 2)
-- X520 serial number
ATVParam o atvParamX520SerialNumber = PrintableString
-- PCKS-9 email address
ATVParam o atvParamPCKS9Email = IA5String
-- domain component
ATVParam o atvParamDomainComponent = IA5String

ATVParam' : AnyDefinedByOID
ATVParam' o = ATVParam o ((-, TLV.val o) ∈? Supported)

ATV = DefinedByOID λ o → ATVParam o ((-, TLV.val o) ∈? Supported)

pattern mkATVFields o p bs≡ = mkOIDDefinedFields o p bs≡

RawATVParam : Raw₁ RawOID ATVParam'
toRawATVParam : ∀ {@0 bs₁} {o : OID bs₁} {@0 bs₂} → (o? : Dec ((-, TLV.val o) ∈ Supported)) → ATVParam o o? bs₂ → Raw₁.D RawATVParam (Raw.to RawOID o)

Raw₁.D RawATVParam ro =
    Raw.D RawDirectoryString
  ⊎ Raw.D RawPrintableString
  ⊎ Raw.D (RawΣₚ₁ RawPrintableString (TLVSizeBounded sizePrintableString 2 2))
  ⊎ Raw.D RawPrintableString
  ⊎ Raw.D RawIA5String
Raw₁.to RawATVParam o {bs} = toRawATVParam ((-, TLV.val o) ∈? Supported)

toRawATVParam {o} (no ¬p) p =
  inj₁ (Raw.to RawDirectoryString p)
toRawATVParam {o} (yes (here px)) p =
  inj₂ (inj₁ (Raw.to RawPrintableString p))
toRawATVParam {o} (yes (there (here px))) p =
  inj₂ (inj₂ (inj₁ (Raw.to (RawΣₚ₁ RawPrintableString (TLVSizeBounded sizePrintableString 2 2)) p)))
toRawATVParam {o} (yes (there (there (here px)))) p =
  inj₂ ∘ inj₂ ∘ inj₂ ∘ inj₁ $ Raw.to RawPrintableString p
toRawATVParam {o} (yes (there (there (there (here px))))) p =
  inj₂ (inj₂ (inj₂ (inj₁ $ Raw.to RawIA5String p)))
toRawATVParam {o} (yes (there (there (there (there (here px)))))) p =
  inj₂ (inj₂ (inj₂ (inj₂ $ Raw.to RawIA5String p)))

RawATV : Raw ATV
RawATV = RawDefinedByOID RawATVParam
