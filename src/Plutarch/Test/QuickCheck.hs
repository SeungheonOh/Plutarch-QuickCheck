{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

module Plutarch.Test.QuickCheck (
    type IsPLam,
    type IsLast,
    type PTT,
    type TestableFun,
    type PLamArgs,
    type PA,
    type PB,
    type PC,
    FromPFunN (..),
    fromPFun, 
    haskEquiv',
    haskEquiv,
    shrinkPLift,
    arbitraryPLift,

    PFun (..),
    pattern PFn,
    applyPFun,
    plamTable,
    plamFinite,

    TestableTerm (..), 
    PArbitrary (..),
    pconstantT,
    pliftT,
) where

import Plutarch.Test.QuickCheck.Function
import Plutarch.Test.QuickCheck.Instances

import Control.Arrow
import Data.Kind
import Data.List
import Data.Universe
import Generics.SOP hiding (And)
import Plutarch
import "liqwid-plutarch-extra" Plutarch.Extra.List
import Plutarch.Extra.Maybe
import Plutarch.Lift
import Plutarch.Prelude
import Plutarch.Show
import Test.QuickCheck
import Test.QuickCheck.Function

-- | @since x.y.z
data PTermType
    = LastPFunction
    | LastPTerm
    | PFunction
    | PTerm

-- | @since x.y.z
type family PTT' isplam end :: PTermType where
    PTT' True True = LastPFunction
    PTT' False True = LastPTerm
    PTT' True False = PFunction
    PTT' False False = PTerm

-- | @since x.y.z
type PTT (p :: S -> Type) = PTT' (IsPLam p) (IsLast p)

-- | @since x.y.z
type family IsPLam (p :: S -> Type) :: Bool where
    IsPLam ((a :--> b) :--> c) = True
    IsPLam _ = False

-- | @since x.y.z
type family IsLast (p :: S -> Type) :: Bool where
    IsLast (a :--> PBool) = True
    IsLast _ = False

{- | Finds Haskell level TestableTerm equivlance of Plutarch
     functions. This TypeFamily expects the input Plutarch functions to
     be returning @PBool@ at the end.

     This is used to find type signatures for @quickCheck@able
     functions from Plutarch terms like @Term s (a :--> b :--> PBool)@.

 @since x.y.z
-}
type family TestableFun (b :: PTermType) (p :: S -> Type) where
    TestableFun _ PBool = TestableTerm PBool
    TestableFun PTerm (a :--> b) = TestableTerm a -> (TestableFun (PTT b) b)
    TestableFun LastPTerm (a :--> b) = TestableTerm a -> (TestableFun (PTT b) b)
    TestableFun PFunction ((a :--> b) :--> c) = PFun a b -> (TestableFun (PTT c) c)
    TestableFun LastPFunction ((a :--> b) :--> c) = PFun a b -> (TestableFun (PTT c) c)

{- | Convert Plutarch function into testable Haskell function that takes
     `TestableTerm`. It also converts plutarch function into `PFun`.

 @since x.y.z
-}
class FromPFunN (a :: S -> Type) (b :: S -> Type) (c :: PTermType) where
    fromPFun' :: Proxy c -> (forall s. Term s (a :--> b)) -> TestableFun c (a :--> b)

-- | @since x.y.z
instance
    forall a b.
    ( PLift a
    , PLift b
    ) =>
    FromPFunN (a :--> b) PBool LastPFunction
    where
    fromPFun' _ f = \(PFn x) -> TestableTerm $ f # x

-- | @since x.y.z
instance FromPFunN a PBool LastPTerm where
    fromPFun' _ f = \(TestableTerm x) -> TestableTerm $ f # x

-- | @since x.y.z
instance
    forall a b c d e.
    ( c ~ (d :--> e)
    , PLift a
    , PLift b
    , FromPFunN d e (PTT c)
    ) =>
    FromPFunN (a :--> b) c PFunction
    where
    fromPFun' _ f = \(PFn x) -> fromPFun' (Proxy @(PTT c)) $ f # x

-- | @since x.y.z
instance
    forall a b c d.
    ( b ~ (c :--> d)
    , FromPFunN c d (PTT b)
    ) =>
    FromPFunN a b PTerm
    where
    fromPFun' _ f = \(TestableTerm x) -> fromPFun' (Proxy @(PTT b)) $ f # x

{- | Converts Plutarch Functions into `Testable` Haskell function of TestableTerms.

 @since x.y.z
-}
fromPFun ::
    forall a b c.
    ( c ~ PTT (a :--> b)
    , FromPFunN a b c
    ) =>
    (forall s. Term s (a :--> b)) ->
    TestableFun c (a :--> b)
fromPFun f = fromPFun' (Proxy @(PTT (a :--> b))) f

{- | Extracts all @TestableTerm@s from give Plutarch function.

 @since x.y.z
-}
type family PLamArgs (p :: S -> Type) :: [Type] where
    PLamArgs (a :--> b) = TestableTerm a : (PLamArgs b)
    PLamArgs _ = '[]

{- | Make property by directly comparing behavior of Plutarch function
     to Haskell counterpart.  This function will expect all Plutarch
     types to be `plift`able and `pshow`able.  With given TestableTerm
     generator, it will generate value for each arguments. Then, it
     will apply generated value and lifted value to Plutarch and
     haskell function. Once all arguments are applied, It will check
     the equality of results.

 @since x.y.z
-}
class (PLamArgs p ~ args) => HaskEquiv (h :: Type) (p :: S -> Type) args where
    haskEquiv :: h -> TestableTerm p -> NP Gen args -> Property

-- | @since x.y.z
instance
    forall ha hb pa pb hbArgs.
    ( PLamArgs pb ~ hbArgs
    , HaskEquiv hb pb hbArgs
    , PLifted pa ~ ha
    , PLift pa
    , PShow pa
    ) =>
    HaskEquiv (ha -> hb) (pa :--> pb) (TestableTerm pa ': hbArgs)
    where
    haskEquiv h (TestableTerm p) (g :* gs) =
        forAll g $ \(TestableTerm x) -> haskEquiv (h $ plift x) (TestableTerm $ p # x) gs

-- | @since x.y.z
instance (PLamArgs p ~ '[], PLift p, PLifted p ~ h, Eq h) => HaskEquiv h p '[] where
    haskEquiv h (TestableTerm p) _ = property $ plift p == h

{- | Simplified version of `haskEquiv`. It will use arbitrary instead of
     asking custom generators.

 @since x.y.z
-}
haskEquiv' ::
    forall h p args.
    ( PLamArgs p ~ args
    , HaskEquiv h p args
    , All Arbitrary args
    ) =>
    h ->
    (forall s. Term s p) ->
    Property
haskEquiv' h p = haskEquiv h (TestableTerm p) $ hcpure (Proxy @Arbitrary) arbitrary

type PA :: S -> Type
type PA = PInteger

type PB :: S -> Type
type PB = PInteger

type PC :: S -> Type
type PC = PInteger

{-
This shinker "simplifies" underlaying plutarch representation. When
shrinking List, this shinker is always preferable.
-}
shrinkPLift ::
    forall a.
    ( PLift a
    , Arbitrary (PLifted a)
    ) =>
    TestableTerm a ->
    [TestableTerm a]
shrinkPLift = fmap pconstantT . shrink . pliftT

arbitraryPLift ::
    forall a.
    ( PLift a
    , Arbitrary (PLifted a)
    ) =>
    Gen (TestableTerm a)
arbitraryPLift = pconstantT <$> arbitrary
