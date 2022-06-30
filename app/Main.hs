{-# LANGUAGE ExistentialQuantification #-}

module Main where

import Test.QuickCheck
import Test.Tasty
import Test.Tasty.QuickCheck
import Test.Tasty.Plutarch.Property

import Plutarch
import Plutarch.Evaluate
import Plutarch.Prelude
import Plutarch.Show
import Plutarch.Lift
import Plutarch.Api.V1

import Lib

test :: TestableTerm PInteger -> TestableTerm PInteger -> TestableTerm PInteger -> TestableTerm PBool
test (TestableTerm x) (TestableTerm y) (TestableTerm z) = TestableTerm $ x + y #< z + 10

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
commutativitySub = plam $ \x-> plet (pfstBuiltin # x) $ \a -> plet (psndBuiltin # x) $ \b ->
    a + b #== b + a

commutativityProp :: Property
commutativityProp = peqProperty (pconstant True) (arbitrary :: Gen (Integer, Integer)) (const []) commutativitySub

main = defaultMain $
    testGroup "performance" $
    [ testGroup "Commutativity of addition" $
      [ testGroup "new" [testProperty "" (withMaxSuccess 50000 (fromPFun commutativity))]
      , testGroup "new - worse method" [testProperty "" (withMaxSuccess 50000 (fromPFun commutativitySub))]      
      , testGroup "old" [testProperty "" (withMaxSuccess 50000 (commutativityProp))]
      ]
    ]

pIllegal :: Term s (PInteger :--> PInteger :--> PInteger :--> PString)
pIllegal = plam $ \x y z -> "asdF"

test4 = fromPFun pfunction
