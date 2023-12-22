open import Armor.Binary
open import Armor.Data.X509.GeneralNames.GeneralName.TCB
open import Armor.Data.X509.Name
open import Armor.Data.X690-DER
import      Armor.Grammar.Definitions
import      Armor.Grammar.Properties
import      Armor.Grammar.Sum
open import Armor.Prelude
open import Data.Nat.Properties
  hiding (_≟_)

module Armor.Data.X509.GeneralNames.GeneralName.Properties where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Properties  UInt8
open Armor.Grammar.Sum         UInt8

iso : Iso GeneralNameRep GeneralName
proj₁ iso = equivalentGeneralName
proj₁ (proj₂ iso) (Sum.inj₁ x) = refl
proj₁ (proj₂ iso) (Sum.inj₂ (Sum.inj₁ x)) = refl
proj₁ (proj₂ iso) (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x))) = refl
proj₁ (proj₂ iso) (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x)))) = refl
proj₁ (proj₂ iso) (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x))))) = refl
proj₁ (proj₂ iso) (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x)))))) = refl
proj₁ (proj₂ iso) (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x))))))) = refl
proj₁ (proj₂ iso) (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x)))))))) = refl
proj₁ (proj₂ iso) (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ x)))))))) = refl
proj₂ (proj₂ iso) (oname x) = refl
proj₂ (proj₂ iso) (rfcname x) = refl
proj₂ (proj₂ iso) (dnsname x) = refl
proj₂ (proj₂ iso) (x400add x) = refl
proj₂ (proj₂ iso) (dirname x) = refl
proj₂ (proj₂ iso) (ediname x) = refl
proj₂ (proj₂ iso) (uri x) = refl
proj₂ (proj₂ iso) (ipadd x) = refl
proj₂ (proj₂ iso) (rid x) = refl

nonempty : NonEmpty GeneralName
nonempty (oname ()) refl
nonempty (rfcname ()) refl
nonempty (dnsname ()) refl
nonempty (x400add ()) refl
nonempty (dirname ()) refl
nonempty (ediname ()) refl
nonempty (uri ()) refl
nonempty (ipadd ()) refl
nonempty (rid ()) refl

@0 nosubstrings : NoSubstrings GeneralName
nosubstrings x (oname x₁) (oname x₂) = ‼ TLV.nosubstrings x x₁ x₂
nosubstrings x (oname x₁) (rfcname x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (oname x₁) (dnsname x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (oname x₁) (x400add x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (oname x₁) (dirname x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (oname x₁) (ediname x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (oname x₁) (uri x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (oname x₁) (ipadd x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (oname x₁) (rid x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (rfcname x₁) (oname x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (rfcname x₁) (rfcname x₂) = ‼ TLV.nosubstrings x x₁ x₂
nosubstrings x (rfcname x₁) (dnsname x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (rfcname x₁) (x400add x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (rfcname x₁) (dirname x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (rfcname x₁) (ediname x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (rfcname x₁) (uri x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (rfcname x₁) (ipadd x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (rfcname x₁) (rid x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (dnsname x₁) (oname x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (dnsname x₁) (rfcname x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (dnsname x₁) (dnsname x₂) = ‼ TLV.nosubstrings x x₁ x₂
nosubstrings x (dnsname x₁) (x400add x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (dnsname x₁) (dirname x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (dnsname x₁) (ediname x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (dnsname x₁) (uri x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (dnsname x₁) (ipadd x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (dnsname x₁) (rid x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (x400add x₁) (oname x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (x400add x₁) (rfcname x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (x400add x₁) (dnsname x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (x400add x₁) (x400add x₂) = ‼ TLV.nosubstrings x x₁ x₂
nosubstrings x (x400add x₁) (dirname x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (x400add x₁) (ediname x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (x400add x₁) (uri x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (x400add x₁) (ipadd x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (x400add x₁) (rid x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (dirname x₁) (oname x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (dirname x₁) (rfcname x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (dirname x₁) (dnsname x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (dirname x₁) (x400add x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (dirname x₁) (dirname x₂) = ‼ TLV.nosubstrings x x₁ x₂
nosubstrings x (dirname x₁) (ediname x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (dirname x₁) (uri x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (dirname x₁) (ipadd x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (dirname x₁) (rid x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (ediname x₁) (oname x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (ediname x₁) (rfcname x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (ediname x₁) (dnsname x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (ediname x₁) (x400add x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (ediname x₁) (dirname x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (ediname x₁) (ediname x₂) = ‼ TLV.nosubstrings x x₁ x₂
nosubstrings x (ediname x₁) (uri x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (ediname x₁) (ipadd x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (ediname x₁) (rid x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (uri x₁) (oname x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (uri x₁) (rfcname x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (uri x₁) (dnsname x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (uri x₁) (x400add x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (uri x₁) (dirname x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (uri x₁) (ediname x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (uri x₁) (uri x₂) = ‼ TLV.nosubstrings x x₁ x₂
nosubstrings x (uri x₁) (ipadd x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (uri x₁) (rid x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (ipadd x₁) (oname x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (ipadd x₁) (rfcname x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (ipadd x₁) (dnsname x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (ipadd x₁) (x400add x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (ipadd x₁) (dirname x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (ipadd x₁) (ediname x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (ipadd x₁) (uri x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (ipadd x₁) (ipadd x₂) = ‼ TLV.nosubstrings x x₁ x₂
nosubstrings x (ipadd x₁) (rid x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (rid x₁) (oname x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (rid x₁) (rfcname x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (rid x₁) (dnsname x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (rid x₁) (x400add x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (rid x₁) (dirname x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (rid x₁) (ediname x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (rid x₁) (uri x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (rid x₁) (ipadd x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (rid x₁) (rid x₂) = ‼ TLV.nosubstrings x x₁ x₂

@0 unambiguous : Unambiguous GeneralName
unambiguous =
    Iso.unambiguous iso
      (Sum.unambiguous (TLV.unambiguous OctetString.unambiguousValue)
        ua₁ nc₀)
    where
    Rep₇ = Sum IpAddress RegID
    Rep₆ = Sum URI Rep₇
    Rep₅ = Sum EdipartyName Rep₆
    Rep₄ = Sum DirName Rep₅
    Rep₃ = Sum X400Address Rep₄
    Rep₂ = Sum DnsName Rep₃
    Rep₁ = Sum RfcName Rep₂

    nc₇ : NoConfusion IpAddress RegID
    nc₇ = TLV.noconfusion λ ()

    ua₇ : Unambiguous Rep₇
    ua₇ = Sum.unambiguous
            (TLV.unambiguous OctetString.unambiguousValue)
            (TLV.unambiguous
              (SequenceOf.Bounded.unambiguous OID.Sub.unambiguous OID.Sub.nonempty OID.Sub.nosubstrings))
            nc₇

    nc₆ : NoConfusion URI Rep₇
    nc₆ = Sum.noconfusion{A = URI} (TLV.noconfusion (λ ())) (TLV.noconfusion λ ())

    ua₆ : Unambiguous Rep₆
    ua₆ = Sum.unambiguous (TLV.unambiguous IA5String.unambiguous) ua₇ nc₆

    nc₅ : NoConfusion EdipartyName Rep₆
    nc₅ = Sum.noconfusion{A = EdipartyName}
            (TLV.noconfusion λ ())
            (Sum.noconfusion{A = EdipartyName} (TLV.noconfusion (λ ()))
              (TLV.noconfusion λ ()))

    ua₅ : Unambiguous Rep₅
    ua₅ = Sum.unambiguous (TLV.unambiguous OctetString.unambiguousValue)
            ua₆ nc₅

    nc₄ : NoConfusion DirName Rep₅
    nc₄ = Sum.noconfusion {A = DirName}
            (TLV.noconfusion λ ())
            (Sum.noconfusion {A = DirName}
              (TLV.noconfusion λ ())
              (Sum.noconfusion {A = DirName}
                (TLV.noconfusion λ ()) (TLV.noconfusion λ ())))

    ua₄ : Unambiguous Rep₄
    ua₄ = Sum.unambiguous (TLV.unambiguous Name.unambiguous) ua₅ nc₄

    nc₃ : NoConfusion X400Address Rep₄
    nc₃ = Sum.noconfusion {A = X400Address}
            (TLV.noconfusion λ ())
            (Sum.noconfusion{A = X400Address}
              (TLV.noconfusion λ ())
              (Sum.noconfusion{A = X400Address}
                (TLV.noconfusion λ ())
                (Sum.noconfusion {A = X400Address}
                  (TLV.noconfusion λ ()) (TLV.noconfusion λ ()))))

    ua₃ : Unambiguous Rep₃
    ua₃ = Sum.unambiguous (TLV.unambiguous OctetString.unambiguousValue)
            ua₄ nc₃

    nc₂ : NoConfusion DnsName Rep₃
    nc₂ = Sum.noconfusion{A = DnsName}
            (TLV.noconfusion λ ())
            (Sum.noconfusion {A = DnsName}
              (TLV.noconfusion λ ())
              (Sum.noconfusion {A = DnsName}
                (TLV.noconfusion λ ())
                (Sum.noconfusion {A = DnsName} (TLV.noconfusion λ ())
                  (Sum.noconfusion {A = DnsName} (TLV.noconfusion λ ()) (TLV.noconfusion λ ())))))

    ua₂ : Unambiguous Rep₂
    ua₂ = Sum.unambiguous (TLV.unambiguous IA5String.unambiguous)
            ua₃ nc₂

    nc₁ : NoConfusion RfcName Rep₂
    nc₁ = Sum.noconfusion {A = RfcName}
            (TLV.noconfusion λ ())
            (Sum.noconfusion {A = RfcName}
              (TLV.noconfusion λ ())
              (Sum.noconfusion {A = RfcName}
                (TLV.noconfusion λ ())
                (Sum.noconfusion {A = RfcName}
                  (TLV.noconfusion λ ())
                  (Sum.noconfusion {A = RfcName}
                    (TLV.noconfusion λ ())
                    (Sum.noconfusion {A = RfcName}
                      (TLV.noconfusion λ ()) (TLV.noconfusion λ ()))))))

    ua₁ : Unambiguous Rep₁
    ua₁ = Sum.unambiguous (TLV.unambiguous IA5String.unambiguous)
            ua₂ nc₁

    nc₀ : NoConfusion OtherName Rep₁
    nc₀ = Sum.noconfusion {A = OtherName} (TLV.noconfusion λ ())
            (Sum.noconfusion {A = OtherName} (TLV.noconfusion λ ())
              (Sum.noconfusion {A = OtherName} (TLV.noconfusion λ ())
                (Sum.noconfusion {A = OtherName} (TLV.noconfusion λ ())
                  (Sum.noconfusion {A = OtherName} (TLV.noconfusion λ ())
                    (Sum.noconfusion {A = OtherName} (TLV.noconfusion λ ())
                      (Sum.noconfusion {A = OtherName} (TLV.noconfusion λ ())
                        (TLV.noconfusion λ ())))))))

@0 nonmalleable : NonMalleable RawGeneralName
nonmalleable = Iso.nonmalleable iso RawGeneralNameRep nm
    where
    Rep₇ = RawSum (RawTLV Tag.A87 RawOctetStringValue) (RawTLV Tag.A88 RawOIDValue)
    Rep₆ = RawSum (RawTLV Tag.A86 RawIA5StringValue) Rep₇
    Rep₅ = RawSum (RawTLV Tag.AA5 RawOctetStringValue) Rep₆
    Rep₄ = RawSum (RawTLV Tag.AA4 RawName) Rep₅
    Rep₃ = RawSum (RawTLV Tag.AA3 RawOctetStringValue) Rep₄
    Rep₂ = RawSum (RawTLV Tag.A82 RawIA5StringValue) Rep₃
    Rep₁ = RawSum (RawTLV Tag.A81 RawIA5StringValue) Rep₂

    nm :  NonMalleable RawGeneralNameRep
    nm =  Sum.nonmalleable{ra = RawTLV _ RawOctetStringValue}{rb = Rep₁} (TLV.nonmalleable OctetString.nonmalleableValue)
         (Sum.nonmalleable{ra = RawTLV _ RawIA5StringValue}  {rb = Rep₂} (TLV.nonmalleable IA5String.nonmalleableValue)
         (Sum.nonmalleable{ra = RawTLV _ RawIA5StringValue}  {rb = Rep₃} (TLV.nonmalleable IA5String.nonmalleableValue)
         (Sum.nonmalleable{ra = RawTLV _ RawOctetStringValue}{rb = Rep₄} (TLV.nonmalleable OctetString.nonmalleableValue)
         (Sum.nonmalleable{ra = RawTLV _ RawName}            {rb = Rep₅} (TLV.nonmalleable Name.nonmalleable)
         (Sum.nonmalleable{ra = RawTLV _ RawOctetStringValue}{rb = Rep₆} (TLV.nonmalleable OctetString.nonmalleableValue)
         (Sum.nonmalleable{ra = RawTLV _ RawIA5StringValue}  {rb = Rep₇} (TLV.nonmalleable IA5String.nonmalleableValue)
         (Sum.nonmalleable{ra = RawTLV _ RawOctetStringValue}            (TLV.nonmalleable OctetString.nonmalleableValue)
                                                                         (TLV.nonmalleable OID.nonmalleableValue))))))))
