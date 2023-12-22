import Armor.Data.X509.PublicKey.Alg.Eq
import Armor.Data.X509.PublicKey.Alg.TCB
import Armor.Data.X509.PublicKey.Alg.Parser
import Armor.Data.X509.PublicKey.Alg.Properties

module Armor.Data.X509.PublicKey.Alg where

open Armor.Data.X509.PublicKey.Alg.TCB public
  hiding (getOID)

module Alg where
  open Armor.Data.X509.PublicKey.Alg.Eq         public
  open Armor.Data.X509.PublicKey.Alg.Parser     public
  open Armor.Data.X509.PublicKey.Alg.Properties public
  open Armor.Data.X509.PublicKey.Alg.TCB        public
    using (getOID)
