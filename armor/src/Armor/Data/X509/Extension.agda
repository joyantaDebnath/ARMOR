import Armor.Data.X509.Extension.AIA
import Armor.Data.X509.Extension.AKI
import Armor.Data.X509.Extension.BC
import Armor.Data.X509.Extension.CRLDistPoint
import Armor.Data.X509.Extension.CertPolicy
import Armor.Data.X509.Extension.EKU
import Armor.Data.X509.Extension.Eq
import Armor.Data.X509.Extension.IAN
import Armor.Data.X509.Extension.INAP
import Armor.Data.X509.Extension.KU
import Armor.Data.X509.Extension.NC
import Armor.Data.X509.Extension.PC
import Armor.Data.X509.Extension.PM
import Armor.Data.X509.Extension.Parser
import Armor.Data.X509.Extension.Properties
import Armor.Data.X509.Extension.SAN
import Armor.Data.X509.Extension.SKI
import Armor.Data.X509.Extension.TCB
  hiding (equivalent)

module Armor.Data.X509.Extension where

open import Armor.Data.X509.Extension.Parser public
open import Armor.Data.X509.Extension.TCB    public
  hiding (module Extension)

module Extension where
  open Armor.Data.X509.Extension.AIA           public
  open Armor.Data.X509.Extension.AKI           public
  open Armor.Data.X509.Extension.BC            public
  open Armor.Data.X509.Extension.CRLDistPoint  public
  open Armor.Data.X509.Extension.CertPolicy    public
  open Armor.Data.X509.Extension.EKU           public
  open Armor.Data.X509.Extension.Eq            public
  open Armor.Data.X509.Extension.IAN           public
  open Armor.Data.X509.Extension.INAP          public
  open Armor.Data.X509.Extension.KU            public
  open Armor.Data.X509.Extension.NC            public
  open Armor.Data.X509.Extension.PC            public
  open Armor.Data.X509.Extension.PM            public
  open Armor.Data.X509.Extension.Properties    public
  open Armor.Data.X509.Extension.SAN           public
  open Armor.Data.X509.Extension.SKI           public
  open Armor.Data.X509.Extension.TCB           public
    hiding (equivalent)
  open Armor.Data.X509.Extension.TCB.Extension public
