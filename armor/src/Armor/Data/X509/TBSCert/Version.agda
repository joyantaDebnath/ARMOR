import Armor.Data.X509.TBSCert.Version.Eq
import Armor.Data.X509.TBSCert.Version.Parser
import Armor.Data.X509.TBSCert.Version.Properties
import Armor.Data.X509.TBSCert.Version.TCB

module Armor.Data.X509.TBSCert.Version where

open Armor.Data.X509.TBSCert.Version.TCB    public
  using (Version ; [0]ExplicitVersion ; v1[0]ExplicitVersion ; Raw[0]ExplicitVersion ; v1 ; v2 ; v3)

module Version where
  open Armor.Data.X509.TBSCert.Version.Eq         public
  open Armor.Data.X509.TBSCert.Version.Parser     public
  open Armor.Data.X509.TBSCert.Version.Properties public
