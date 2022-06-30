{-# LANGUAGE RankNTypes, DefaultSignatures, TypeFamilies, UndecidableInstances, TypeApplications, DeriveAnyClass, AllowAmbiguousTypes, TypeFamilyDependencies, QuantifiedConstraints, ImpredicativeTypes #-}

module Lib where

import qualified GHC.Exts as Exts
import Test.Tasty
import Test.Tasty.QuickCheck hiding (NonZero)
import Test.QuickCheck
import Data.ByteString

import qualified Data.Text as T
import Plutarch
import Plutarch.DataRepr
import Plutarch.List
import Plutarch.Rational
import Plutarch.Unsafe
import Plutarch.Evaluate
import Plutarch.Prelude
import Plutarch.Show
import Plutarch.Lift
import Plutarch.Api.V1
import Plutarch.Api.V1.Time

import Test.Tasty.Plutarch.Property

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

{- | TestableTerm is a wrapper for closed Plutarch term. This
   abstraction allows Plutarch values can be generated via QuickCheck
   Generator.

 @since x.y.z
-}
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
         in T.unpack . T.intercalate " " $ trace
    
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
deriving instance PArbitrary PUnit

-- | @since x.y.z
instance PArbitrary PByteString where
    parbitrary = do
        len <- chooseInt (0, 64)
        bs <- genByteString len
        return $ TestableTerm $ pconstant bs

genByteStringUpto :: Int -> Gen ByteString
genByteStringUpto m = sized go
  where
    go :: Int -> Gen ByteString
    go s = chooseInt (0, min m s) >>= genByteString

genByteString :: Int -> Gen ByteString
genByteString l = Exts.fromList <$> vectorOf l arbitrary    

-- | @since x.y.z
instance PArbitrary PRational where
    parbitrary = do
        (TestableTerm x) <- parbitrary
        (TestableTerm y) <- parbitrary
        return $ TestableTerm $ pcon $ PRational x y

-- | @since x.y.z
instance PArbitrary PString where
    parbitrary = (\x -> TestableTerm (pconstant (T.pack x))) <$> arbitrary

-- | @since x.y.z
instance PArbitrary a => PArbitrary (PMaybe a) where
    parbitrary = do
        (TestableTerm x) <- parbitrary
        elements [TestableTerm $ pcon $ PJust x, TestableTerm $ pcon $ PNothing]
        
-- | @since x.y.z
instance {-# OVERLAPPING #-} (PArbitrary a, PArbitrary b) => PArbitrary (PEither a b) where
    parbitrary = do
        (TestableTerm x) <- parbitrary
        (TestableTerm y) <- parbitrary
        elements [TestableTerm $ pcon $ PRight x, TestableTerm $ pcon $ PLeft y]        
        
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
    ) => PArbitrary (PBuiltinPair a b) where
    parbitrary = (\x -> TestableTerm (pconstant x)) <$> arbitrary

-- | @since x.y.z
-- I have no clue why this needs overlapping. GHC insists it is
-- overlapped with PListLike instance.
instance {-# OVERLAPPING #-} 
    ( PArbitrary a
    , PArbitrary b
    ) => PArbitrary (PPair a b) where
    parbitrary = do
        (TestableTerm x) <- parbitrary
        (TestableTerm y) <- parbitrary
        return $ TestableTerm $ pcon $ PPair x y

-- | @since x.y.z
instance
    ( PArbitrary a
    , PListLike b
    , PElemConstraint b a
    ) => PArbitrary (b a) where
    parbitrary = do
        len <- arbitrary
        xs <- vectorOf len parbitrary
        return $ constrPList xs
        where
          constrPList :: [TestableTerm a] -> TestableTerm (b a)
          constrPList [] = TestableTerm $ pnil
          constrPList ((TestableTerm x): xs) =
              let (TestableTerm rest) = constrPList xs
              in TestableTerm $ pcons # x # rest

-- | @since x.y.z
instance PArbitrary PPOSIXTime where
    parbitrary = do
        (TestableTerm x) <- parbitrary
        return $ TestableTerm $ pcon $ PPOSIXTime x

-- | @since x.y.z
instance {-# OVERLAPPING #-} (PIsData a, PArbitrary a) => PArbitrary (PExtended a) where
    parbitrary = do
        (TestableTerm x) <- parbitrary
        elements $
            [ TestableTerm $ pcon $ PNegInf pdnil
            , TestableTerm $ pcon $ PFinite $ pdcons @"_0" # (pdata x) # pdnil
            , TestableTerm $ pcon $ PPosInf pdnil
            ]

-- | @since x.y.z
instance {-# OVERLAPPING #-} (PIsData a, PArbitrary a) => PArbitrary (PLowerBound a) where
    parbitrary = do
        (TestableTerm ex) <- parbitrary
        (TestableTerm cl) <- parbitrary
        return $ TestableTerm $ pcon $ PLowerBound $
            pdcons @"_0" # (pdata ex) #$ pdcons @"_1" # (pdata cl) # pdnil

-- | @since x.y.z
instance {-# OVERLAPPING #-} (PIsData a, PArbitrary a) => PArbitrary (PUpperBound a) where
    parbitrary = do
        (TestableTerm ex) <- parbitrary
        (TestableTerm cl) <- parbitrary
        return $ TestableTerm $ pcon $ PUpperBound $
            pdcons @"_0" # (pdata ex) #$ pdcons @"_1" # (pdata cl) # pdnil

-- | @since x.y.z
instance {-# OVERLAPPING #-} (PIsData a, PArbitrary a) => PArbitrary (PInterval a) where
    parbitrary = do
        (TestableTerm lo) <- parbitrary
        (TestableTerm up) <- parbitrary
        return $ TestableTerm $ pcon $ PInterval $
            pdcons @"from" # (pdata lo) #$ pdcons @"to" # (pdata up) # pdnil
