{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE UndecidableInstances #-}

module Lib where

import Data.ByteString
import qualified GHC.Exts as Exts
import Test.QuickCheck hiding (NonZero, Positive, Sorted)
import Test.Tasty
import Test.Tasty.QuickCheck hiding (NonZero, Positive, Sorted)

import qualified Data.Text as T
import Plutarch
import Plutarch.Api.V1
import qualified Plutarch.Api.V1.AssocMap as Assoc
import qualified "plutarch" Plutarch.Api.V1.Value as Value
import Plutarch.Api.V1.Time
import Plutarch.Api.V1.Tuple
import Plutarch.Builtin
import Plutarch.DataRepr
import Plutarch.Evaluate
import Plutarch.Extra.Map.Unsorted
import Plutarch.Lift
import Plutarch.List
import Plutarch.Prelude
import Plutarch.Rational
import Plutarch.Show
import Plutarch.Unsafe

import Test.Tasty.Plutarch.Property

type family TestableFun (p :: S -> Type) = r | r -> p where
    TestableFun PBool = TestableTerm PBool
    TestableFun (a :--> (b :: S -> Type)) = TestableTerm a -> (TestableFun b)

class FromPFunN (a :: S -> Type) (b :: S -> Type) where
    fromPFun :: (forall s. Term s (a :--> b)) -> TestableFun (a :--> b)

instance {-# OVERLAPPING #-} FromPFunN a PBool where
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
    (forall (s :: S). Term s a -> Term s b) ->
    TestableTerm a ->
    TestableTerm b
liftTestable f (TestableTerm x) = TestableTerm $ f x

lift2Testable ::
    forall (a :: S -> Type) (b :: S -> Type) (c :: S -> Type).
    (forall (s :: S). Term s a -> Term s b -> Term s c) ->
    TestableTerm a ->
    TestableTerm b ->
    TestableTerm c
lift2Testable f (TestableTerm x) (TestableTerm y) = TestableTerm $ f x y

instance (forall (s :: S). Num (Term s a)) => Num (TestableTerm a) where
    (+) = lift2Testable (+)
    (*) = lift2Testable (*)
    abs = liftTestable abs
    negate = liftTestable negate
    signum = liftTestable signum
    fromInteger i = TestableTerm $ (fromInteger i :: Term s a)

instance (forall (s :: S). Eq (Term s a)) => Eq (TestableTerm a) where
    (TestableTerm x) == (TestableTerm y) = x == y

-- instance PShow a => Show (TestableTerm a) where
--     show (TestableTerm term) =
--         let (_, _, trace) = evalScript $ compile $ ptraceError (pshow term)
--          in T.unpack . T.intercalate " " $ trace

-- TODO: Need a better way for this.
instance Show (TestableTerm a) where
    show _ = "<no print instance defined>"

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
instance (PArbitrary p, PIsData p) => PArbitrary (PAsData p) where
    parbitrary = do
        (TestableTerm x) <- parbitrary
        return $ TestableTerm $ pdata x

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
instance (PIsData a, PArbitrary a) => PArbitrary (PMaybeData a) where
    parbitrary = do
        (TestableTerm x) <- parbitrary
        elements $
            [ TestableTerm $ pcon $ PDJust $ pdcons @"_0" # (pdata x) # pdnil
            , TestableTerm $ pcon $ PDNothing pdnil
            ]

-- | @since x.y.z
instance (PArbitrary a, PArbitrary b) => PArbitrary (PEither a b) where
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
    ) =>
    PArbitrary (PBuiltinPair a b)
    where
    parbitrary = (\x -> TestableTerm (pconstant x)) <$> arbitrary

-- | @since x.y.z
instance
    {-# OVERLAPPING #-}
    ( PArbitrary a
    , PArbitrary b
    , PIsData a
    , PIsData b
    ) =>
    PArbitrary (PBuiltinPair (PAsData a) (PAsData b))
    where
    parbitrary = do
        (TestableTerm x) <- parbitrary
        return $ TestableTerm $ pfromData $ pbuiltinPairFromTuple (pdata x)

-- | @since x.y.z
instance
    ( PArbitrary a
    , PArbitrary b
    , PIsData a
    , PIsData b
    ) =>
    PArbitrary (PMap Unsorted a b)
    where
    parbitrary = do
        (TestableTerm x) <- parbitrary
        return $ TestableTerm $ pcon $ PMap x

-- | @since x.y.z
instance
    ( PArbitrary a
    , PArbitrary b
    , PIsData a
    , PIsData b
    , POrd a
    ) =>
    PArbitrary (PMap Sorted a b)
    where
    parbitrary = do
        (TestableTerm x) <- parbitrary
        return $ TestableTerm $ psort # (pcon $ PMap x)

-- | @since x.y.z
instance
    ( PArbitrary a
    , PArbitrary b
    ) =>
    PArbitrary (PPair a b)
    where
    parbitrary = do
        (TestableTerm x) <- parbitrary
        (TestableTerm y) <- parbitrary
        return $ TestableTerm $ pcon $ PPair x y

-- | @since x.y.z
instance
    ( PArbitrary a
    , PArbitrary b
    , PIsData a
    , PIsData b
    ) =>
    PArbitrary (PTuple a b)
    where
    parbitrary = do
        (TestableTerm x) <- parbitrary
        (TestableTerm y) <- parbitrary
        return $ TestableTerm $ ptuple # (pdata x) # (pdata y)

genPListLike :: forall b a. (PArbitrary a, PIsListLike b a) => Gen (TestableTerm (b a))
genPListLike = do
    -- Need to find a better way to limit the size of list
    -- So that it doesn't break Plutarch's memory limit.
    len <- chooseInt (0, 10)
    xs <- vectorOf len parbitrary
    return $ constrPList xs
  where
    constrPList :: [TestableTerm a] -> TestableTerm (b a)
    constrPList [] = TestableTerm $ pnil
    constrPList ((TestableTerm x) : xs) =
        let (TestableTerm rest) = constrPList xs
         in TestableTerm $ pcons # x # rest

-- | @since x.y.z
instance forall a. (PArbitrary a, PIsListLike PBuiltinList a) => PArbitrary (PBuiltinList a) where
    parbitrary = genPListLike

-- | @since x.y.z
instance forall a. (PArbitrary a, PIsListLike PList a) => PArbitrary (PList a) where
    parbitrary = genPListLike

-- | @since x.y.z
instance PArbitrary PPOSIXTime where
    parbitrary = do
        (TestableTerm x) <- parbitrary
        return $ TestableTerm $ pcon $ PPOSIXTime x

-- | @since x.y.z
instance (PIsData a, PArbitrary a) => PArbitrary (PExtended a) where
    parbitrary = do
        (TestableTerm x) <- parbitrary
        elements $
            [ TestableTerm $ pcon $ PNegInf pdnil
            , TestableTerm $ pcon $ PFinite $ pdcons @"_0" # (pdata x) # pdnil
            , TestableTerm $ pcon $ PPosInf pdnil
            ]

-- | @since x.y.z
instance (PIsData a, PArbitrary a) => PArbitrary (PLowerBound a) where
    parbitrary = do
        (TestableTerm ex) <- parbitrary
        (TestableTerm cl) <- parbitrary
        return $
            TestableTerm $
                pcon $
                    PLowerBound $
                        pdcons @"_0" # (pdata ex) #$ pdcons @"_1" # (pdata cl) # pdnil

-- | @since x.y.z
instance (PIsData a, PArbitrary a) => PArbitrary (PUpperBound a) where
    parbitrary = do
        (TestableTerm ex) <- parbitrary
        (TestableTerm cl) <- parbitrary
        return $
            TestableTerm $
                pcon $
                    PUpperBound $
                        pdcons @"_0" # (pdata ex) #$ pdcons @"_1" # (pdata cl) # pdnil

-- | @since x.y.z
instance (PIsData a, PArbitrary a) => PArbitrary (PInterval a) where
    parbitrary = do
        (TestableTerm lo) <- parbitrary
        (TestableTerm up) <- parbitrary
        return $
            TestableTerm $
                pcon $
                    PInterval $
                        pdcons @"from" # (pdata lo) #$ pdcons @"to" # (pdata up) # pdnil

-- | @since x.y.z
instance PArbitrary PPubKeyHash where
    parbitrary = do
        -- PubKeyHash should be 28 bytes long
        bs <- genByteString 28
        return $ TestableTerm $ pcon $ PPubKeyHash $ pconstant bs

-- | @since x.y.z
instance PArbitrary PValidatorHash where
    parbitrary = do
        -- PubKeyHash should be 28 bytes long
        bs <- genByteString 28
        return $ TestableTerm $ pcon $ PValidatorHash $ pconstant bs

-- | @since x.y.z
instance PArbitrary PStakeValidatorHash where
    parbitrary = do
        -- PubKeyHash should be 28 bytes long
        bs <- genByteString 28
        return $ TestableTerm $ pcon $ PStakeValidatorHash $ pconstant bs

-- | @since x.y.z
instance PArbitrary PCredential where
    parbitrary = do
        (TestableTerm pk) <- parbitrary
        (TestableTerm vh) <- parbitrary
        elements $
            [ TestableTerm $ pcon $ PScriptCredential $ pdcons @"_0" # (pdata vh) # pdnil
            , TestableTerm $ pcon $ PPubKeyCredential $ pdcons @"_0" # (pdata pk) # pdnil
            ]

-- | @since x.y.z
instance PArbitrary PStakingCredential where
    parbitrary = do
        (TestableTerm cred) <- parbitrary
        (TestableTerm x) <- parbitrary
        (TestableTerm y) <- parbitrary
        (TestableTerm z) <- parbitrary
        elements $
            [ TestableTerm $ pcon $ PStakingHash $ pdcons @"_0" # (pdata cred) # pdnil
            , TestableTerm $
                pcon $
                    PStakingPtr $
                        pdcons @"_0" # (pdata x)
                            #$ pdcons @"_1" # (pdata y)
                            #$ pdcons @"_2" # (pdata z) # pdnil
            ]

-- | @since x.y.z
instance PArbitrary PAddress where
    parbitrary = do
        (TestableTerm cred) <- parbitrary
        (TestableTerm scred) <- parbitrary
        return $
            TestableTerm $
                pcon $
                    PAddress $
                        pdcons @"credential" # (pdata cred)
                            #$ pdcons @"stakingCredential" # (pdata scred) # pdnil

-- | @since x.y.z
instance PArbitrary PCurrencySymbol where
    parbitrary = do
        (TestableTerm cs) <- parbitrary
        return $ TestableTerm $ pcon $ PCurrencySymbol cs

-- | @since x.y.z
instance PArbitrary PTokenName where
    parbitrary = do
        len <- chooseInt (1, 32)
        tn <- genByteString len
        return $ TestableTerm $ pcon $ PTokenName $ pconstant tn

-- | @since x.y.z
instance PArbitrary (PValue Unsorted NoGuarantees) where
    parbitrary = do
        (TestableTerm val) <- parbitrary
        return $ TestableTerm $ pcon $ PValue val

-- | @since x.y.z
instance PArbitrary (PValue Unsorted NonZero) where
    parbitrary = do
        (TestableTerm val) <- parbitrary
        return $
            TestableTerm $
                pcon $
                    PValue $
                        Assoc.pmap # (plam $ \x -> Assoc.pfilter # (plam $ \y -> pnot # (y #== 0)) # x) # val

-- | @since x.y.z
instance PArbitrary (PValue Unsorted Positive) where
    parbitrary = do
        (TestableTerm val) <- parbitrary
        return $
            TestableTerm $
                pcon $
                    PValue $
                        Assoc.pmap # (plam $ \x -> Assoc.pfilter # (plam $ \y -> pnot # (0 #< y)) # x) # val

-- | @since x.y.z
instance PArbitrary (PValue Sorted NoGuarantees) where
    parbitrary = do
        (TestableTerm val) <- parbitrary
        return $ TestableTerm $ pcon $ PValue val

-- | @since x.y.z
instance PArbitrary (PValue Sorted NonZero) where
    parbitrary = do
        (TestableTerm val) <- parbitrary
        return $
            TestableTerm $
            Value.pnormalize #$
                pcon $
                    PValue $
                        Assoc.pmap # (plam $ \x -> Assoc.pfilter # (plam $ \y -> pnot # (y #== 0)) # x) # val

-- | @since x.y.z
instance PArbitrary (PValue Sorted Positive) where
    parbitrary = do
        (TestableTerm val) <- (parbitrary :: Gen (TestableTerm (PValue Sorted NonZero)))
        return $
            TestableTerm $
                pcon $
                    PValue $
                        Assoc.pmap # (plam $ \x -> Assoc.pfilter # (plam $ \y -> (0 #<= y)) # x) # pto val
