{-# LANGUAGE ExistentialQuantification #-}
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

test3 = fromPFun $ plam $ \(x :: Term s PInteger) -> pconstant False

pfunction :: Term s (PMaybe PString :--> PBool)
pfunction = plam $ \x -> pmatch x $ \case
    PJust _ -> pcon PFalse
    PNothing -> pcon PTrue

pfunction2 :: Term s (PInteger :--> PInteger :--> PBool)
pfunction2 = plam $ \x y -> x #== y

commutativity :: Term s (PInteger :--> PInteger :--> PBool)
commutativity = plam $ \x y -> x + y #== y + x

commutativitySub :: Term s ((PBuiltinPair PInteger PInteger) :--> PBool)
commutativitySub = plam $ \x -> plet (pfstBuiltin # x) $ \a -> plet (psndBuiltin # x) $ \b ->
    a + b #== b + a

commutativityProp :: Property
commutativityProp = peqProperty (pconstant True) (arbitrary :: Gen (Integer, Integer)) (const []) commutativitySub

selfEq :: PEq a => Term s (a :--> PBool)
selfEq = plam $ \x -> x #== x

unsorted :: forall s. Term s (PMap Unsorted PInteger PInteger :--> PBool)
unsorted = plam $ \x ->
    selfEq #$ Assoc.passertSorted # ((punsafeCoerce x) :: Term s (PMap Sorted PInteger PInteger))

sorted :: Term s (PMap Sorted PInteger PInteger :--> PBool)
sorted = plam $ \x ->
    selfEq #$ Assoc.passertSorted # x

-- performance
--    : FAIL
--     *** Failed! (after 5 tests):
--     Exception:
--       plift failed: erring term: An error has occurred:  User error:
--       The provided Plutus code called 'error'.
--       CallStack (from HasCallStack):
--         error, called at ./Plutarch/Lift.hs:127:35 in plutarch-1.1.0-4EQ12CHnVAYBJLNZJcjv1f:Plutarch.Lift
--         plift, called at src/Lib.hs:53:43 in study-0.1.0.0-inplace:Lib
--     [(4,-3), (4,-4), (-2,2), (3,-3)]
--     Use --quickcheck-replay=574348 to reproduce.

-- | Assert the value is properly sorted and normalized.
passertSorted :: Term s (PValue Sorted b :--> PValue 'Sorted 'NonZero)
passertSorted = phoistAcyclic $
    plam $ \value ->
        pif
            ( Assoc.pany
                # ( plam $
                        \submap ->
                            Assoc.pany # plam (#== 0) #$ Assoc.passertSorted # submap
                  )
                # pto value
            )
            (ptraceError "Abnormal Value")
            (pcon $ PValue $ Assoc.passertSorted # pto value)

sortedValue :: forall s. Term s (PValue Sorted NonZero :--> PBool)
sortedValue = plam $ \x ->
    selfEq #$ Value.passertSorted # x

positiveSortedValue :: forall s. Term s (PValue Sorted Positive :--> PBool)
positiveSortedValue = plam $ \x ->
    selfEq #$ Value.passertPositive # (punsafeCoerce x)

main =
    defaultMain $
        testGroup "performance" $
            [ --     expectFail $ testProperty "unsorted should not be sorted" $ withMaxSuccess 5000 (fromPFun unsorted)
              -- , testProperty "sorted should be sorted" $ withMaxSuccess 5000 (fromPFun sorted)
                testProperty "Sorted Values should be sorted" $ withMaxSuccess 1000 (fromPFun sortedValue)
              , testProperty "Sorted Values should be sorted" $ withMaxSuccess 1000 (fromPFun positiveSortedValue)              
              -- testGroup "Commutativity of addition" $
              -- [ testGroup "new" [testProperty "" (withMaxSuccess 50000 (fromPFun commutativity))]
              -- , testGroup "new - worse method" [testProperty "" (withMaxSuccess 50000 (fromPFun commutativitySub))]
              -- , testGroup "old" [testProperty "" (withMaxSuccess 50000 (commutativityProp))]
              -- ]
            ]

pIllegal :: Term s (PInteger :--> PInteger :--> PInteger :--> PString)
pIllegal = plam $ \x y z -> "asdF"

test4 = fromPFun pfunction
