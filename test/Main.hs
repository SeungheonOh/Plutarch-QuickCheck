{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE TypeApplications #-}

module Main where

import Lib
import Plutarch
import Plutarch.Prelude
import Plutarch.Api.V1 (
    AmountGuarantees (NoGuarantees, NonZero, Positive),
    KeyGuarantees (Sorted, Unsorted),
    PMap,
    PValue,
 )
import "plutarch" Plutarch.Api.V1.AssocMap qualified as Assoc (
    passertSorted,
 )
import "plutarch" Plutarch.Api.V1.Value qualified as Value (
    passertPositive,
    passertSorted,
 )
import "liqwid-plutarch-extra" Plutarch.Extra.List    
import Plutarch.Evaluate ()
import Plutarch.Lift ()
import Plutarch.Prelude (PBool, PEq (..), PInteger)
import Plutarch.Show ()
import Plutarch.Unsafe (punsafeCoerce)
import Test.QuickCheck (
    Arbitrary (arbitrary),
    Property,
    Testable,
    forAllShow,
    resize,
    forAll,
    forAllShrink,
    shrink,
 )
import Test.Tasty (defaultMain, testGroup)
import Test.Tasty.ExpectedFailure (expectFail)
import Test.Tasty.Plutarch.Property ()
import Test.Tasty.QuickCheck (testProperty, Gen, withMaxSuccess )
import "liqwid-plutarch-extra" Plutarch.Extra.List (preverse)
import Generics.SOP

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
    haskEquiv (+1) (TestableTerm addone) (customGen :* Nil)
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
testProp3 = forAllShrink arbitrary shrink $ fromPFun test
    where
      test :: forall s. Term s (PList PInteger :--> PBool)
      test = plam $ \x -> pnot #$ pelem # 5 # x #&& plength # x #== 5 

test2 :: Property
test2 = forAllShrink arbitrary shrink $ test
    where
      test :: [Integer] -> Bool
      test x = not $ elem 5 x && length x == 3

main =
    defaultMain $
        testGroup "Tests" $
            [ testGroup "Values" $
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
            , testGroup "Performance comp" $
                [ expectFail $ testProperty "Plutarch w/ shrinker" $ withMaxSuccess 50000 $ testProp 
                , expectFail $ testProperty "Plutarch w/ memory problem" $ withMaxSuccess 50000 $ testProp3
                , expectFail $ testProperty "Haskell reference" $ withMaxSuccess 50000 $ test2   
                ]
            ]
