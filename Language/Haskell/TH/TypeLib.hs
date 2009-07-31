{-# LANGUAGE TemplateHaskell #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Language.Haskell.TH.TypeLib
-- Copyright   :  (c) SAM Group, KTH/ICT/ECS 2007-2008
-- License     :  BSD-style (see the file LICENSE)
-- 
-- Maintainer  :  forsyde-dev@ict.kth.se
-- Stability   :  experimental
-- Portability :  portable
--
-- This module provides basic functions related to Template-Haskell's 'Type'.
-- 
-----------------------------------------------------------------------------
module Language.Haskell.TH.TypeLib 
 (reAppT,
  dynTHType,
  thTypeOf,
  typeRep2Type,
  tyCon2Type) 
 where

import Data.Dynamic
import Data.Typeable
import Language.Haskell.TH
import Language.Haskell.TH.Lib
import Text.Regex.Posix ((=~))

-- | Rebuild a type out of a constructor, its argument types and its context
--   (inverse of 'unAppT')
reAppT :: (TypeQ, [TypeQ])  -- ^ (Constructor, type arguments, context)
       -> TypeQ                     -- ^ resulting 'Type'
-- Monomorphic types
reAppT (cons, args) = foldl1 appT (cons:args)

-------------------------------------------------------------------
-- Transforming Data.Typeable.TypeRep into Language.Haskell.TH.Type
-------------------------------------------------------------------  

-- | Obtain the Template Haskel type of a dynamic object
dynTHType :: Dynamic -> TypeQ
dynTHType = typeRep2Type . dynTypeRep

-- | Give the template haskell 'Type' of a Typeable object
thTypeOf :: Typeable a => a -> TypeQ
thTypeOf = typeRep2Type . typeOf

-- | Translate a 'TypeRep' to a Template Haskell 'Type'
typeRep2Type :: TypeRep -> TypeQ
typeRep2Type rep = let (con, reps) = splitTyConApp rep
  in reAppT (tyCon2Type con, map typeRep2Type reps)
 
-- | Gives the corresponding Template Haskell 'Type' of a 'TyCon'
tyCon2Type :: TyCon -> TypeQ
tyCon2Type = tyConStr2Type . tyConString

----------------------------
-- Internal Helper Functions
----------------------------

-- | transfrom a Typeable type constructor to a Template Haskell Type
tyConStr2Type :: String -> TypeQ
-- NOTE: The tyCon strings of basic types are not qualified and buggy in 
-- some cases.
-- See http://hackage.haskell.org/trac/ghc/ticket/1841
-- FIXME: update this function whenever the bug is fixed
-- FIXME FIXME: This code is incorrect:
-- mkName doesn't generate global names! ''Maybe /= mkName "Data.Maybe.Maybe"
-- in addition global names contain a packagename which cannot be guessed from
-- the type representation.
tyConStr2Type "->" = arrowT
tyConStr2Type  tupStr | tupStr =~ "^,+$" = 
 conT (mkName $ "Data.Tuple.(" ++ tupStr ++ ")")   
tyConStr2Type str  = conT $ mkName str

tyVarToName :: TyVarBndr -> Name
tyVarToName tyvar = name
  where
    name = case tyvar of
      (PlainTV n) -> n
      (KindedTV n _) -> n