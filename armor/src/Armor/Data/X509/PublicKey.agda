import Armor.Data.X509.PublicKey.Alg
import Armor.Data.X509.PublicKey.Eq
import Armor.Data.X509.PublicKey.Parser
import Armor.Data.X509.PublicKey.Properties
import Armor.Data.X509.PublicKey.TCB
import Armor.Data.X509.PublicKey.Val

module Armor.Data.X509.PublicKey where

open Armor.Data.X509.PublicKey.TCB public
  hiding (equivalent ; getOID)

module PublicKey where
  open Armor.Data.X509.PublicKey.Alg        public
  open Armor.Data.X509.PublicKey.Eq         public
  open Armor.Data.X509.PublicKey.Parser     public
  open Armor.Data.X509.PublicKey.Properties public
  open Armor.Data.X509.PublicKey.TCB        public
    using (equivalent ; getOID)
  open Armor.Data.X509.PublicKey.Val        public

