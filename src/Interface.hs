{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

module Interface where

import Control.Arrow
import Data.Kind
import Data.List
import Data.Universe
import Function
import Generics.SOP
import Lib
import Plutarch
import "liqwid-plutarch-extra" Plutarch.Extra.List
import Plutarch.Extra.Maybe
import Plutarch.Lift
import Plutarch.Prelude
import Plutarch.Show
import Test.QuickCheck
import Test.QuickCheck.Function

type family IsPLam (p :: S -> Type) :: Bool where
    IsPLam ((a :--> b) :--> c) = True
    IsPLam _ = False

{- | Finds Haskell level TestableTerm equivlance of Plutarch
     functions. This TypeFamily expects the input Plutarch functions to
     be returning @PBool@ at the end.

     This is used to find type signatures for @quickCheck@able
     functions from Plutarch terms like @Term s (a :--> b :--> PBool)@.

 @since x.y.z
-}
type family TestableFun (b :: Bool) (p :: S -> Type) where
    TestableFun False PBool = TestableTerm PBool
    TestableFun False (a :--> b) = TestableTerm a -> (TestableFun (IsPLam b) b)
    TestableFun True ((a :--> b) :--> c) = PFun a b -> (TestableFun (IsPLam c) c)

{- | Converts Plutarch Functions into `Testable` Haskell function of TestableTerms.

 @since x.y.z
-}
class FromPFunN (a :: S -> Type) (b :: S -> Type) where
    fromPFun :: (forall s. Term s (a :--> b)) -> TestableFun (IsPLam (a :--> b)) (a :--> b)

-- | @since x.y.z
instance
    {-# OVERLAPPING #-}
    forall a b aa ab.
    ( a ~ (aa :--> ab)
    , IsPLam (a :--> b) ~ True
    , PLift aa
    , PLift ab
    ) =>
    FromPFunN (aa :--> ab) PBool
    where
    fromPFun f = \(PFn x) -> TestableTerm $ f # x

-- | @since x.y.z
instance {-# OVERLAPPING #-} (IsPLam (a :--> PBool) ~ False) => FromPFunN a PBool where
    fromPFun f = \(TestableTerm x) -> TestableTerm $ f # x

-- | @since x.y.z
instance
    {-# OVERLAPPING #-}
    forall aa ab a b c d.
    ( b ~ (c :--> d)
    , a ~ (aa :--> ab)
    , IsPLam (a :--> b) ~ True
    , FromPFunN c d
    , PLift aa
    , PLift ab
    ) =>
    FromPFunN (aa :--> ab) b
    where
    fromPFun f = \(PFn x) -> fromPFun $ f # x

-- | @since x.y.z
instance
    {-# OVERLAPPING #-}
    forall a b c d.
    ( b ~ (c :--> d)
    , FromPFunN c d
    , IsPLam (a :--> b) ~ False
    ) =>
    FromPFunN a b
    where
    fromPFun f = \(TestableTerm x) -> fromPFun $ f # x

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
