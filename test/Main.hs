{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

module Main where

import Generics.SOP hiding (Fn, I)
import Plutarch.Test.QuickCheck
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
import Plutarch.Extra.Applicative
import Plutarch.Extra.Functor
import Plutarch.Extra.Identity
import "liqwid-plutarch-extra" Plutarch.Extra.List
import "liqwid-plutarch-extra" Plutarch.Extra.List (preverse)
import Plutarch.Extra.Profunctor
import Plutarch.Extra.Traversable hiding (plength)
import Plutarch.Internal
import Plutarch.Lift
import Plutarch.List
import Plutarch.Prelude
import Plutarch.Prelude (PBool, PEq (..), PInteger)
import Plutarch.Show
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
    quickCheck,
    quickCheckResult,
    resize,
    shrink,
    verbose,
    verboseCheck,
    (.&&.),
    (.||.),
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
    forall (f :: (S -> Type) -> S -> Type).
    ( PFunctor f
    , PEq (f PA)
    , PSubcategory f PA
    , PArbitrary (f PA)
    , IsPLam ((f PA) :--> PBool) ~ False
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
            ( (PA :--> PA)
                :--> (PA :--> PA)
                :--> (f PA)
                :--> PBool
            )
    composition = plam $ \f g x ->
        (pfmap # (plam $ \y -> g #$ f # y) # x) #== (pfmap # g # (pfmap # f # x))

    identity :: Term s ((f PInteger) :--> PBool)
    identity = plam $ \x ->
        (pfmap # (plam id) # x) #== x

applyLaw ::
    forall (f :: (S -> Type) -> S -> Type).
    ( PApply f
    , PApplicative f
    , PEq (f PA)
    , PArbitrary (f PA)
    , PSubcategory f ~ Top
    , IsPLam ((f PA) :--> PBool) ~ False
    ) =>
    Property
applyLaw =
    counterexample
        "composition"
        ( forAllShrink (resize 20 arbitrary) shrink $ \x ->
            forAllShrinkShow (resize 20 arbitrary) shrink (const "") $ \y ->
                forAllShrinkShow (resize 20 arbitrary) shrink (const "") $ \z ->
                    (fromPFun composition) x y z
        )
        .&&. counterexample
            "interchange 1"
            ( forAllShrink (resize 20 arbitrary) shrink $ \x ->
                forAllShrinkShow (resize 20 arbitrary) shrink (const "") $ \y ->
                    forAllShrinkShow (resize 20 arbitrary) shrink (const "") $ \z ->
                        (fromPFun interchange1) x y z
            )
        .&&. counterexample
            "interchange 2"
            ( forAllShrink (resize 20 arbitrary) shrink $ \x ->
                forAllShrinkShow (resize 20 arbitrary) shrink (const "") $ \y ->
                    forAllShrinkShow (resize 20 arbitrary) shrink (const "") $ \z ->
                        (fromPFun interchange2) x y z
            )
  where
    compose :: Term s ((c :--> d) :--> (b :--> c) :--> b :--> d)
    compose = plam $ \f g x -> f #$ g # x
    compose' :: Term s ((b :--> c) :--> (c :--> d) :--> b :--> d)
    compose' = plam $ \g f x -> f #$ g # x

    composition :: Term s ((PA :--> PA) :--> (PA :--> PA) :--> f PA :--> PBool)
    composition = plam $ \f' g' x ->
        let f = ppure @f # f'
            g = ppure @f # f'
         in ((compose #<$> f) #<*> g #<*> x) #== (f #<*> (g #<*> x))

    interchange1 :: Term s ((PA :--> PA) :--> (PA :--> PA) :--> f PA :--> PBool)
    interchange1 = plam $ \f' g x ->
        let f = ppure @f # f'
         in (f #<*> (g #<$> x)) #== (((compose' # g) #<$> f) #<*> x)

    interchange2 :: Term s ((PA :--> PA) :--> (PA :--> PA) :--> f PA :--> PBool)
    interchange2 = plam $ \f' g x ->
        let f = ppure @f # f'
         in (g #<$> (f #<*> x)) #== (((compose # g) #<$> f) #<*> x)

applicativeLaw ::
    forall (f :: (S -> Type) -> S -> Type).
    ( PEq (f PA)
    , PShow (f PA)
    , PApplicative f
    , PSubcategory f ~ Top
    , PArbitrary (f PA)
    , IsPLam ((f PA) :--> PBool) ~ False
    ) =>
    Property
applicativeLaw =
    counterexample
        "Identity"
        (forAllShrinkShow (resize 20 arbitrary) shrink (const "") (fromPFun identity))
        .&&. counterexample
            "Homomorphism"
            ( forAllShrink (resize 20 arbitrary) shrink $ \x ->
                forAllShrinkShow (resize 20 arbitrary) shrink (const "") $ \y ->
                    (fromPFun homomorphism) x y
            )
        .&&. counterexample
            "Interchange"
            ( forAllShrink (resize 20 arbitrary) shrink $ \x ->
                forAllShrinkShow (resize 20 arbitrary) shrink (const "") $ \y ->
                    (fromPFun interchange) x y
            )
        .&&. counterexample
            "composition"
            ( forAllShrink (resize 20 arbitrary) shrink $ \x ->
                forAllShrink (resize 20 arbitrary) shrink $ \y ->
                    forAllShrinkShow (resize 20 arbitrary) shrink (const "") $ \z ->
                        (fromPFun composition) x y z
            )
  where
    compose :: Term s ((c :--> d) :--> (b :--> c) :--> (b :--> d))
    compose = plam $ \f g x -> f #$ g # x

    identity ::
        Term s ((f PA) :--> PBool)
    identity = plam $ \x -> ((ppure # plam id) #<*> x) #== x

    homomorphism ::
        Term s ((PA :--> PA) :--> PA :--> PBool)
    homomorphism = plam $ \f x -> (ppure @f # f) #<*> (ppure @f # x) #== ppure @f # (f # x)

    interchange ::
        Term s ((PA :--> PA) :--> PA :--> PBool)
    interchange = plam $ \f' x ->
        let f = ppure @f # f'
         in f #<*> (ppure @f # x) #== (ppure @f # (plam $ \g -> g # x)) #<*> f

    composition ::
        Term s ((PA :--> PA) :--> (PA :--> PA) :--> (f PA) :--> PBool)
    composition = plam $ \f' g' x ->
        let f = ppure @f # f'
            g = ppure @f # g'
         in (ppure @f # compose) #<*> f #<*> g #<*> x #== f #<*> (g #<*> x)

traversableLaw ::
    forall (t :: (S -> Type) -> S -> Type).
    ( PTraversable t
    , PSubcategory t ~ Top
    , PEq (t PA)
    , PArbitrary (t PA)
    , IsPLam ((t PA) :--> PBool) ~ False
    ) =>
    Property
traversableLaw =
    counterexample "identity" $
        forAllShrinkShow arbitrary shrink (const "") (fromPFun identity)
  where
    identity :: Term s (t PA :--> PBool)
    identity = plam $ \x ->
        ptraverse @t # (plam $ \x -> pcon $ PIdentity x) # x #== (pcon $ PIdentity x)

{- Sadly, It's impossible to make an arbitrary applicative
   transformation (Applicative f, Applicative g) => f a -> g a.
-}
-- nutrality :: Term s ((PList (t PA) :--> PA) :--> (PA :--> PList PA) :--> t PA :--> PInteger)
-- nutrality = plam $ \f g x ->
--     -- f # (ptraverse @t # g # x)--  #== --
--     ptraverse @t # (compose # f # g) # x

main = do
    let n = 100
    defaultMain $
        testGroup "Tests" $
            [ testGroup "Functors" $
                [ testProperty "PBuiltinList is Functor" $ withMaxSuccess n $ (functorLaw @PBuiltinList)
                , testProperty "PMaybeData is Functor" $ withMaxSuccess n $ (functorLaw @PMaybeData)
                , testProperty "PMaybe is Functor" $ withMaxSuccess n $ (functorLaw @PMaybe)
                , testProperty "PEither is Functor" $ withMaxSuccess n $ (functorLaw @(PEither PUnit))
                , testProperty "PList is Functor" $ withMaxSuccess n $ (functorLaw @PList)
                , testProperty "PMap is Functor" $ withMaxSuccess n $ (functorLaw @(PMap Unsorted PInteger))
                ]
            , testGroup "Apply" $
                [ testProperty "PBuiltinList is Apply" $ withMaxSuccess n $ (applyLaw @PList)
                , testProperty "PMaybe is Apply" $ withMaxSuccess n $ (applyLaw @PMaybe)
                , testProperty "PEither is Apply" $ withMaxSuccess n $ (applyLaw @(PEither PUnit))
                ]
            , testGroup "Applicative" $
                [ testProperty "PBuiltinList is Applicative" $ withMaxSuccess n $ (applicativeLaw @PList)
                , testProperty "PMaybe is Applicative" $ withMaxSuccess n $ (applicativeLaw @PMaybe)
                , testProperty "PEither is Applicative" $ withMaxSuccess n $ (applicativeLaw @(PEither PUnit))
                ]
            , testGroup "Traversable" $
                [ testProperty "PBuiltinList is Traversable" $ withMaxSuccess n $ (traversableLaw @PList)
                , testProperty "PMaybe is Traversable" $ withMaxSuccess n $ (traversableLaw @PMaybe)
                , testProperty "PEither is Traversable" $ withMaxSuccess n $ (traversableLaw @(PEither PUnit))
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
