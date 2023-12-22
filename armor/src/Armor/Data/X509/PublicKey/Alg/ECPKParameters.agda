import Armor.Data.X509.PublicKey.Alg.ECPKParameters.ECParameters
import Armor.Data.X509.PublicKey.Alg.ECPKParameters.Parser
import Armor.Data.X509.PublicKey.Alg.ECPKParameters.Properties
import Armor.Data.X509.PublicKey.Alg.ECPKParameters.TCB

module Armor.Data.X509.PublicKey.Alg.ECPKParameters where

open Armor.Data.X509.PublicKey.Alg.ECPKParameters.TCB    public
  hiding (module ECPKParameters ; equivalent)

module ECPKParameters where
  open Armor.Data.X509.PublicKey.Alg.ECPKParameters.ECParameters public
  open Armor.Data.X509.PublicKey.Alg.ECPKParameters.Parser       public
  open Armor.Data.X509.PublicKey.Alg.ECPKParameters.Properties   public
  open Armor.Data.X509.PublicKey.Alg.ECPKParameters.TCB          public
    using (equivalent)
