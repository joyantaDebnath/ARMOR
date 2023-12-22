open import Armor.Binary
open import Armor.Data.X690-DER.TLV
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Definitions.NonMalleable
open import Armor.Prelude

module Armor.Data.X690-DER.OctetString.TCB where

open Armor.Grammar.Definitions.NonMalleable UInt8

-- https://www.itu.int/rec/T-REC-X.690-202102-I/en
-- 8.7.1 The encoding of an octetstring value shall be either primitive or constructed at the option of the sender.
-- NOTE – Where it is necessary to transfer part of an octet string before the entire octetstring is available, the constructed encoding is
-- used.
-- 8.7.2 The primitive encoding contains zero, one or more contents octets equal in value to the octets in the data value, in
-- the order they appear in the data value, and with the most significant bit of an octet of the data value aligned with the most
-- significant bit of an octet of the contents octets.
-- 8.7.3 The contents octets for the constructed encoding shall consist of zero, one, or more encodings.
-- NOTE – Each such encoding includes identifier, length, and contents octets, and may include end-of-contents octets if it is constructed.
-- 8.7.3.1 To encode an octetstring value in this way, it is segmented. Each segment shall consist of a series of consecutive
-- octets of the value. There shall be no significance placed on the segment boundaries.
-- NOTE – A segment may be of size zero, i.e. contain no octets.
-- 8.7.3.2 Each encoding in the contents octets shall represent a segment of the overall octetstring, the encoding arising from
-- a recursive application of this subclause. In this recursive application, each segment is treated as if it were an octetstring value.
-- The encodings of the segments shall appear in the contents octets in the order in which their octets appear in the overall value.
-- NOTE 1 – As a consequence of this recursion, each encoding in the contents octets may itself be primitive or constructed. However,
-- such encodings will usually be primitive.
-- NOTE 2 – In particular, the tags in the contents octets are always universal class, number 4

OctetStringValue : @0 List UInt8 → Set
OctetStringValue = Singleton

OctetString = TLV Tag.OctetString OctetStringValue

RawOctetStringValue : Raw OctetStringValue
Raw.D RawOctetStringValue = List UInt8
Raw.to RawOctetStringValue = ↑_

RawOctetString : Raw OctetString
RawOctetString = RawTLV _ RawOctetStringValue
