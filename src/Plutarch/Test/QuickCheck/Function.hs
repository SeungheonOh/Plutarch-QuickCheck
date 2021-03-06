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

module Plutarch.Test.QuickCheck.Function (
    PFun (..),
    pattern PFn,
    applyPFun,
    plamTable,
    plamFinite,
) where

import Plutarch.Test.QuickCheck.Instances

import Control.Arrow
import Data.Kind
import Data.List
import Data.Universe
import Plutarch
import "liqwid-plutarch-extra" Plutarch.Extra.List
import Plutarch.Extra.Maybe
import Plutarch.Lift
import Plutarch.Prelude
import Test.QuickCheck
import Test.QuickCheck.Function

data PFun (a :: S -> Type) (b :: S -> Type) where
    PFun ::
        (PLift a, PLift b) =>
        [(PLifted a, PLifted b)] ->
        PLifted b ->
        (TestableTerm (a :--> b)) ->
        PFun a b

pattern PFn f <- (unTestableTerm . applyPFun -> f)

applyPFun :: (PLift a, PLift b) => PFun a b -> TestableTerm (a :--> b)
applyPFun (PFun _ _ f) = f

mkPFun ::
    forall (a :: S -> Type) (b :: S -> Type) (s :: S).
    ( PLift a
    , PLift b
    , PEq a
    ) =>
    [(PLifted a, PLifted b)] ->
    PLifted b ->
    PFun a b
mkPFun t d = PFun t d $ TestableTerm $ plamTable t d

instance
    forall (a :: S -> Type) (b :: S -> Type) (s :: S).
    ( PLift a
    , PLift b
    , Arbitrary (PLifted a)
    , Arbitrary (PLifted b)
    , CoArbitrary (PLifted a)
    , Eq (PLifted a)
    , PEq a
    ) =>
    Arbitrary (PFun a b)
    where
    arbitrary = sized $ \r -> do
        xs <- vectorOf r (arbitrary :: Gen (PLifted a))
        ys <- sequenceA $ ($ (arbitrary :: Gen (PLifted b))) . coarbitrary <$> xs
        let table = zipWith (,) xs ys

        d <- arbitrary :: Gen (PLifted b)
        return $ mkPFun (nubBy (\x y -> fst x == fst y) table) d

    shrink (PFun t d _) =
        [mkPFun t' d' | (t', d') <- shrink (t, d)]

instance
    forall (a :: S -> Type) (b :: S -> Type) (s :: S).
    ( PLift a
    , PLift b
    , Show (PLifted a)
    , Show (PLifted b)
    ) =>
    Show (PFun a b)
    where
    show = showPFun

showPFun ::
    forall (a :: S -> Type) (b :: S -> Type) (s :: S).
    ( PLift a
    , PLift b
    , Show (PLifted a)
    , Show (PLifted b)
    ) =>
    PFun a b ->
    String
showPFun (PFun t d _) =
    "{\n"
        ++ intercalate
            ", \n"
            ( [ show x ++ " -> " ++ show c
              | (x, c) <- t
              ]
                ++ ["_ -> " ++ show d]
            )
        ++ "\n}"

plamTable ::
    forall (a :: S -> Type) (b :: S -> Type) (s :: S).
    ( PLift a
    , PLift b
    , PEq a
    ) =>
    [(PLifted a, PLifted b)] ->
    PLifted b ->
    Term s (a :--> b)
plamTable t d = plam $ \x -> pmaybe # pconstant d # (plookup # x # pconstant t)

plamFinite ::
    forall (a :: S -> Type) (b :: S -> Type) (s :: S).
    ( Finite (PLifted a)
    , PLift a
    , PLift b
    , PEq a
    ) =>
    (PLifted a -> PLifted b) ->
    Term s (a :--> b)
plamFinite f = plam $ \x -> pfromJust #$ plookup # x # table
  where
    table :: Term s (PBuiltinList (PBuiltinPair a b))
    table = pconstant $ (id &&& f) <$> universeF
