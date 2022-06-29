{-# LANGUAGE RankNTypes, DefaultSignatures, TypeFamilies, UndecidableInstances, TypeApplications, DeriveAnyClass, AllowAmbiguousTypes, TypeFamilyDependencies, QuantifiedConstraints #-}

module Lib where

import Test.Tasty
import Test.Tasty.QuickCheck hiding (NonZero)
import Test.QuickCheck

import qualified Data.Text as T
import Plutarch
import Plutarch.Unsafe
import Plutarch.Evaluate
import Plutarch.Prelude
import Plutarch.Show
import Plutarch.Lift
import Plutarch.Api.V1

import Test.Tasty.Plutarch.Property

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

type family TestableFun (p :: S -> Type) = r | r -> p where
    TestableFun PBool = TestableTerm PBool
    TestableFun (a :--> (b :: S -> Type)) = TestableTerm a -> (TestableFun b)

class FromPFunN (a :: S -> Type) (b :: S -> Type) where
    fromPFun :: (forall s. Term s (a :--> b)) -> TestableFun (a :--> b)

instance  {-# OVERLAPPING #-} FromPFunN a PBool where
    fromPFun f = \(TestableTerm x) -> TestableTerm $ f # x

instance forall a b c d. (b ~ (c :--> d), FromPFunN c d) => FromPFunN a b where
    fromPFun f = \(TestableTerm x) -> fromPFun $ f # x

instance Testable (TestableTerm PBool) where
    property (TestableTerm t) = property (plift t)
    
newtype TestableTerm a = TestableTerm (forall s. Term s a)

liftTestable ::
    forall (a :: S -> Type) (b :: S -> Type).
    (forall (s :: S) . Term s a -> Term s b) ->
    TestableTerm a ->
    TestableTerm b
liftTestable f (TestableTerm x) = TestableTerm $ f x

lift2Testable ::
    forall (a :: S -> Type) (b :: S -> Type) (c :: S -> Type).
    (forall (s :: S) . Term s a -> Term s b -> Term s c) ->
    TestableTerm a ->
    TestableTerm b ->    
    TestableTerm c
lift2Testable f (TestableTerm x) (TestableTerm y) = TestableTerm $ f x y
    
instance (forall (s :: S) . Num (Term s a)) => Num (TestableTerm a) where
    (+) = lift2Testable (+)
    (*) = lift2Testable (*)
    abs = liftTestable abs
    negate = liftTestable negate
    signum = liftTestable signum
    fromInteger i = TestableTerm $ (fromInteger i :: Term s a)

instance (forall (s :: S) . Eq (Term s a)) => Eq (TestableTerm a) where
    (TestableTerm x) == (TestableTerm y) = x == y

instance PShow a => Show (TestableTerm a) where
    show (TestableTerm term) =
        let (_, _, trace) = evalScript $ compile $ ptraceError (pshow term)
         in show $ T.intercalate " " trace

{- | PArbitrary is Plutarch equivalent of `Arbitrary` typeclass from
   QuickCheck. It generates randomized closed term, which can be used
   to test property over Plutarch code without compiling and evaluating.

   Default implmentation is given for any Plutarch types that
   implments @PLift a@ and @Arbitrary (PLifted a)@. This will Generate
   a haskell value and convert that into Plutarch term using `pconstant`.

   Other more complex Plutarch types, like `PMaybe`, requires mannual
   implmentation. 

 @since x.y.z
-}
class PArbitrary (a :: S -> Type) where
    parbitrary :: Gen (TestableTerm a)
    
    default parbitrary :: (PLift a, Arbitrary (PLifted a)) => Gen (TestableTerm a)
    parbitrary = (\x -> TestableTerm (pconstant x)) <$> arbitrary

{- | Any Plutarch type that implements `PArbitrary a` automatically gets
     `Arbitrary` of @TestableTerm a@. This is an interfacing between
     QuickCheck and Plutarch.

 @since x.y.z
-}
instance PArbitrary p => Arbitrary (TestableTerm p) where
    arbitrary = parbitrary

-- | @since x.y.z
deriving instance PArbitrary PInteger

-- | @since x.y.z
deriving instance PArbitrary PBool

-- | @since x.y.z
instance PArbitrary PString where
    parbitrary = (\x -> TestableTerm (pconstant (T.pack x))) <$> arbitrary

-- | @since x.y.z
instance PArbitrary a => PArbitrary (PMaybe a) where
    parbitrary = do
        (TestableTerm x) <- parbitrary
        elements [TestableTerm $ pcon $ PJust x, TestableTerm $ pcon $ PNothing]
        
{- | Unfortunately, it is impossible to create @PBuiltinPair@ at the
     Plutarch level without getting into manipulating raw Plutus
     data. Instead, it can only be created from haskell level value
     and constanted.

     This limitation limites this generator to only accepting Plutarch
     types that have @PLift@ and @Arbitrary (PLifted a)@. 

 @since x.y.z  
-}
instance
    ( PLift a
    , PLift b
    , Arbitrary (PLifted a, PLifted b)
    ) =>
    PArbitrary (PBuiltinPair a b)
    where
        parbitrary = (\x -> TestableTerm (pconstant x)) <$> arbitrary
