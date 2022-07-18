{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

module Main where

import Function
import Generics.SOP hiding (Fn, I)
import Interface
import Lib
import Plutarch
import Plutarch.Api.V1 (
    AmountGuarantees (NoGuarantees, NonZero, Positive),
    KeyGuarantees (Sorted, Unsorted),
    PMap,
    PMaybeData,
    PValue,
 )
import "plutarch" Plutarch.Api.V1.AssocMap qualified as Assoc (
    passertSorted,
 )
import "plutarch" Plutarch.Api.V1.Value qualified as Value (
    passertPositive,
    passertSorted,
 )
import Plutarch.Evaluate
import Plutarch.Extra.Functor
import "liqwid-plutarch-extra" Plutarch.Extra.List
import "liqwid-plutarch-extra" Plutarch.Extra.List (preverse)
import Plutarch.Internal
import Plutarch.Lift
import Plutarch.List
import Plutarch.Prelude
import Plutarch.Prelude (PBool, PEq (..), PInteger)
import Plutarch.Show
import Plutarch.Show ()
import Plutarch.Unsafe (punsafeCoerce)
import PlutusCore.Data
import Test.QuickCheck (
    Arbitrary (arbitrary),
    Property,
    Testable,
    counterexample,
    forAll,
    forAllShow,
    forAllShrink,
    forAllShrinkShow,
    property,
    resize,
    shrink,
    (.&&.),
 )
import Test.QuickCheck.Function
import Test.Tasty (defaultMain, testGroup)
import Test.Tasty.ExpectedFailure (expectFail)
import Test.Tasty.Plutarch.Property ()
import Test.Tasty.QuickCheck (Fun, Gen, applyFun, testProperty, withMaxSuccess)

selfEq :: PEq a => Term s (a :--> PBool)
selfEq = plam $ \x -> x #== x

prop :: (Arbitrary a, Testable prop) => (a -> prop) -> Property
prop = forAllShow (resize 10 arbitrary) (const "PShow Not Implemented")

unsortedMapProp :: Property
unsortedMapProp =
    prop $ fromPFun unsortedMap
  where
    unsortedMap :: forall s. Term s (PMap Unsorted PInteger PInteger :--> PBool)
    unsortedMap = plam $ \x ->
        selfEq #$ Assoc.passertSorted # ((punsafeCoerce x) :: Term s (PMap Sorted PInteger PInteger))

sortedMapProp :: Property
sortedMapProp =
    prop $ fromPFun sortedMap
  where
    sortedMap :: Term s (PMap Sorted PInteger PInteger :--> PBool)
    sortedMap = plam $ \x ->
        selfEq #$ Assoc.passertSorted # x

sortedValueProp :: Property
sortedValueProp =
    prop $ fromPFun sortedValue
  where
    sortedValue :: forall s. Term s (PValue Sorted NonZero :--> PBool)
    sortedValue = plam $ \x ->
        selfEq #$ Value.passertSorted # x

positiveSortedValueProp :: Property
positiveSortedValueProp =
    prop $ fromPFun positiveSortedValue
  where
    positiveSortedValue :: forall s. Term s (PValue Sorted Positive :--> PBool)
    positiveSortedValue = plam $ \x ->
        selfEq #$ Value.passertPositive # (punsafeCoerce x)

unsortedValueProp :: Property
unsortedValueProp =
    prop $ fromPFun unsortedValue
  where
    unsortedValue :: forall s. Term s (PValue Unsorted NoGuarantees :--> PBool)
    unsortedValue = plam $ \x ->
        selfEq #$ Value.passertSorted # (punsafeCoerce x)

addoneProp :: Property
addoneProp =
    haskEquiv (+ 1) (TestableTerm addone) (customGen :* Nil)
  where
    customGen :: Gen (TestableTerm PInteger)
    customGen = do
        n <- abs <$> arbitrary
        return $ TestableTerm $ pconstant n
    addone :: Term s (PInteger :--> PInteger)
    addone = plam $ \x -> x + 1

reverseProp :: Property
reverseProp =
    haskEquiv' (reverse @Integer) preverse

testProp :: Property
testProp = forAllShrink arbitrary shrink $ fromPFun test
  where
    test :: forall s. Term s (PList PInteger :--> PBool)
    test = plam $ \x -> pnot #$ pelem # 5 # x #&& plength # x #== 3

testProp3 :: Property
testProp3 = forAllShrink arbitrary shrinkPLift $ fromPFun test
  where
    test :: forall s. Term s (PBuiltinList PInteger :--> PBool)
    test = plam $ \x -> pnot #$ pelem # 3 # x #&& plength # x #== 10

testProp6 :: Property
testProp6 = forAllShrink arbitrary shrink $ fromPFun test
  where
    test ::
        Term
            s
            ( (PInteger :--> PBool)
                :--> (PInteger :--> PInteger)
                :--> PBuiltinList PInteger
                :--> PBool
            )
    test = plam $ \f g x ->
        pfilter # f # (pmap # g # x) #== pmap # g # (pfilter # f # x)

functorLaw ::
    forall (a :: (S -> Type) -> S -> Type).
    ( PFunctor a
    , PEq (a PInteger)
    , PSubcategory a PInteger
    , PArbitrary (a PInteger)
    , IsPLam ((a PInteger) :--> PBool) ~ False
    ) =>
    Property
functorLaw =
    counterexample
        "Composition Law"
        ( forAllShrink (resize 10 arbitrary) shrink $ \x ->
            forAllShrink (resize 10 arbitrary) shrink $ \y ->
                forAllShrinkShow
                    (resize 20 arbitrary)
                    (shrink)
                    (const "")
                    $ \z ->
                        (fromPFun composition) x y z
        )
        .&&. counterexample "Identity Law" (forAllShrinkShow arbitrary shrink (const "") (fromPFun identity))
  where
    composition ::
        Term
            s
            ( (PInteger :--> PInteger)
                :--> (PInteger :--> PInteger)
                :--> (a PInteger)
                :--> PBool
            )
    composition = plam $ \f g x ->
        (pfmap # (plam $ \y -> g #$ f # y) # x) #== (pfmap # g # (pfmap # f # x))

    identity :: Term s ((a PInteger) :--> PBool)
    identity = plam $ \x ->
        (pfmap # (plam id) # x) #== x

main = do
    defaultMain $
        testGroup "Tests" $
            [ testGroup "Functors" $
                [ testProperty "PBuiltinList is Functor" $ withMaxSuccess 5000 $ (functorLaw @PBuiltinList)
                , testProperty "PMaybeData is Functor" $ withMaxSuccess 5000 $ (functorLaw @PMaybeData)
                , testProperty "PMaybe is Functor" $ withMaxSuccess 5000 $ (functorLaw @PMaybe)
                , testProperty "PEither is Functor" $ withMaxSuccess 5000 $ (functorLaw @(PEither PUnit))
                , testProperty "PList is Functor" $ withMaxSuccess 5000 $ (functorLaw @PList)
                , testProperty "PMap is Functor" $ withMaxSuccess 5000 $ (functorLaw @(PMap Unsorted PInteger))
                ]
            , testGroup "Values" $
                [ testProperty "Generation of Sorted and Normalized Values" $ withMaxSuccess 1000 $ sortedValueProp
                , testProperty "Generation of Sorted, Normalized, and Positve Values" $ positiveSortedValueProp
                , expectFail $ testProperty "Generation of Unsorted and Un-guaranteed Values" $ unsortedValueProp
                ]
            , testGroup "Map" $
                [ testProperty "Generation of Sorted PMap" $ sortedMapProp
                , expectFail $ testProperty "Generation of Unsorted PMap" $ unsortedMapProp
                ]
            , testGroup "Some examples tests" $
                [ testProperty "add one" $ addoneProp
                , testProperty "add one" $ reverseProp
                ]
            ]
