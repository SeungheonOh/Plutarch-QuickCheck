{-# LANGUAGE ImportQualifiedPost #-}

module Main where

import Test.QuickCheck hiding (NonZero, Positive, Sorted)
import Test.Tasty
import Test.Tasty.ExpectedFailure
import Test.Tasty.Plutarch.Property
import Test.Tasty.QuickCheck hiding (NonZero, Positive, Sorted)

import Plutarch
import Plutarch.Api.V1
import "plutarch" Plutarch.Api.V1.AssocMap qualified as Assoc
import "plutarch" Plutarch.Api.V1.Value qualified as Value
import Plutarch.Evaluate
import Plutarch.Lift
import Plutarch.Prelude
import Plutarch.Show
import Plutarch.Unsafe

import Lib

selfEq :: PEq a => Term s (a :--> PBool)
selfEq = plam $ \x -> x #== x

unsortedMap :: forall s. Term s (PMap Unsorted PInteger PInteger :--> PBool)
unsortedMap = plam $ \x ->
    selfEq #$ Assoc.passertSorted # ((punsafeCoerce x) :: Term s (PMap Sorted PInteger PInteger))

sortedMap :: Term s (PMap Sorted PInteger PInteger :--> PBool)
sortedMap = plam $ \x ->
    selfEq #$ Assoc.passertSorted # x

sortedValue :: forall s. Term s (PValue Sorted NonZero :--> PBool)
sortedValue = plam $ \x ->
    selfEq #$ Value.passertSorted # x

positiveSortedValue :: forall s. Term s (PValue Sorted Positive :--> PBool)
positiveSortedValue = plam $ \x ->
    selfEq #$ Value.passertPositive # (punsafeCoerce x)

unsortedValue :: forall s. Term s (PValue Unsorted NoGuarantees :--> PBool)
unsortedValue = plam $ \x ->
    selfEq #$ Value.passertSorted # (punsafeCoerce x)

main =
    defaultMain $
    testGroup "Tests" $
    [ testGroup "Values" $
      [ testProperty "Generation of Sorted and Normalized Values" $ fromPFun sortedValue
      , testProperty "Generation of Sorted, Normalized, and Positve Values" $ fromPFun positiveSortedValue
      , expectFail $ testProperty "Generation of Unsorted and Un-guaranteed Values" $ fromPFun unsortedValue
      ]
    , testGroup "Map" $
      [ testProperty "Generation of Sorted PMap" $ fromPFun sortedMap
      , expectFail $ testProperty "Generation of Unsorted PMap" $ fromPFun unsortedMap
      ]
    ]

