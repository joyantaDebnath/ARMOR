open import Armor.Binary
open import Armor.Data.X690-DER.Null.TCB
open import Armor.Prelude

module Armor.Data.X509.PublicKey.Alg.RSAPKParameters where

{- https://datatracker.ietf.org/doc/html/rfc3279#section-2.3.1
-- The rsaEncryption OID is intended to be used in the algorithm field
-- of a value of type AlgorithmIdentifier.  The parameters field MUST
-- have ASN.1 type NULL for this algorithm identifier.
-}

RSAPKParameters : @0 List UInt8 → Set
RSAPKParameters = Null
