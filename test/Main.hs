{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE RankNTypes #-}

module Main where

import Lib
import Plutarch
import Plutarch.Internal
import Plutarch.Prelude
import Plutarch.Extra.Stream
import Plutarch.List
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
import Plutarch.Evaluate
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
import Test.Tasty.QuickCheck (testProperty, Gen, withMaxSuccess, Fun, applyFun)
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
testProp3 = forAllShrink arbitrary eshrinkPBIL $ fromPFun test
    where
      test :: forall s. Term s (PBuiltinList PInteger :--> PBool)
      test = plam $ \x -> pnot #$ pelem # 5 # x #&& plength # x #== 30

test2 :: Property
test2 = forAllShrink arbitrary shrink $ test
    where
      test :: [Integer] -> Bool
      test x = not $ elem 5 x && length x == 3

-- ExBudget {exBudgetCPU = ExCPU 663259, exBudgetMemory = ExMemory 2092}
nonSimplified :: Term s PInteger
nonSimplified = phead #$ ptail # aaa
    where
      aaa = pconstant [1..2]

testnonsimp :: Term s PInteger
testnonsimp = phead #$ ptail #$ ptail #$ ptail #$ ptail #$ ptail # aaa
    where
      aaa :: Term s (PList PInteger)
      aaa = let (TestableTerm x) = constrPList (pconstantT <$> ([1..2] :: [Integer])) in x

-- ExBudget {exBudgetCPU = ExCPU 23100, exBudgetMemory = ExMemory 200}
simplified = let (TestableTerm x) = psimplify (TestableTerm nonSimplified) in x

-- testProp4 :: Property
-- testProp4 = forAll arbitrary $ test
--     where
--       test :: (Fun (TestableTerm PInteger) (TestableTerm PBool))
--           -> (Fun (TestableTerm PInteger) (TestableTerm PInteger))
--           -> TestableTerm (PBuiltinList PInteger)
--           -> TestableTerm PBool
--       test f' g' (TestableTerm x) =
--           TestableTerm (pfilter # plam f # (pmap # plam g # x) #== map # plam g # (pfilter # plam f # x))
--           where
--             f :: Term s PInteger -> Term s PBool         
--             f x = let (TestableTerm y) = applyFun f' (TestableTerm x) in y
--             g :: Term s PInteger -> Term s PInteger
--             g x = let (TestableTerm y) = applyFun g' (TestableTerm x) in y

testProp5 :: Property
testProp5 = forAll arbitrary $ test
    where
      test :: (Fun Integer Bool) -> (Fun Integer Integer) -> [Integer] -> Bool
      test f' g' x = filter f (fmap g x) == fmap g (filter f x)
          where
            f = applyFun f'
            g = applyFun g'


-- inf = punsafeCoerce $ pfix $ plam $ \self cons nil -> cons 1 self

main = do
    -- putStrLn "--Nonsimplified"
    -- print $ getTerm $ asRawTerm nonSimplified 0

    -- putStrLn "--deps"
    -- print $ getDeps $ asRawTerm nonSimplified 0
    
    -- putStrLn "--Simplified"    
    -- print $ getTerm $ asRawTerm simplified 0

    -- putStrLn "--Simplified"    
    -- print $ getTerm $ asRawTerm testnonsimp 0
    
    -- putStrLn "--Simplified"    
    -- print $ getDeps $ asRawTerm testnonsimp 0        
    
    -- print $ evalScript (compile nonSimplified)
    -- print $ evalScript (compile simplified)
    -- print $ evalScript (compile testnonsimp)
    defaultMain $
        testGroup "Tests" $
            [ testGroup "Fun gen" $
                [-- testProperty "Fun gen" $ testProp4
                testProperty "Fun gen" $ testProp5
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
            , testGroup "Performance comp" $
                [ expectFail $ testProperty "Plutarch w/ shrinker" $ withMaxSuccess 50000 $ testProp 
                , expectFail $ testProperty "Plutarch w/ memory problem" $ withMaxSuccess 50000 $ testProp3
                , expectFail $ testProperty "Haskell reference" $ withMaxSuccess 50000 $ test2   
                ]
            ]
