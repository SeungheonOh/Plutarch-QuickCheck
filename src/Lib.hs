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
{-# LANGUAGE ViewPatterns #-}

module Lib where

import Data.ByteString (ByteString)
import qualified Data.Text as T (intercalate, pack, unpack)
import qualified GHC.Exts as Exts 
import Plutarch
import Plutarch.Unsafe
import Control.Arrow
import "liqwid-plutarch-extra" Plutarch.Extra.TermCont
import Plutarch.Api.V1 (
    AmountGuarantees (NoGuarantees, NonZero, Positive),
    KeyGuarantees (Sorted, Unsorted),
    PAddress (..),
    PCredential (..),
    PCurrencySymbol (..),
    PExtended (..),
    PInterval (..),
    PLowerBound (..),
    PMap (..),
    PMaybeData (..),
    PPOSIXTime,
    PPubKeyHash (..),
    PStakeValidatorHash (..),
    PStakingCredential (..),
    PTokenName (..),
    PTuple,
    PUpperBound (..),
    PValidatorHash (..),
    PValue (..),
    ptuple,
 )
import qualified Plutarch.Api.V1.AssocMap as Assoc (
    pfilter,
    pmap,
 )
import Plutarch.Extra.Maybe
import Plutarch.Extra.Stream
import Plutarch.Api.V1.Time (PPOSIXTime (PPOSIXTime))
import Plutarch.Api.V1.Tuple 
import qualified "plutarch" Plutarch.Api.V1.Value as Value (
    pnormalize,
 )
import Plutarch.Builtin (
    PAsData,
    PBuiltinList,
    PBuiltinPair,
    PIsData,
    pdata,
    pfromData,
 )
import Plutarch.DataRepr (pdcons, pdnil)
import Plutarch.Evaluate (evalScript)
import Plutarch.Extra.Map.Unsorted (psort)
import Plutarch.Lift (
    PLift,
    PUnsafeLiftDecl ,    
    PUnsafeLiftDecl (PLifted),
    pconstant,
    plift,
 )
import Plutarch.List (PIsListLike, PList, PListLike (pcons, pnil))
import Plutarch.Prelude
import Plutarch.Rational
import Plutarch.Show (PShow)
import Plutarch.Unsafe ()
import Test.QuickCheck hiding (Sorted, NonZero, Positive)
import Generics.SOP    

{- | Finds Haskell level TestableTerm equivlance of Plutarch
     functions. This TypeFamily expects the input Plutarch functions to
     be returning @PBool@ at the end.

     This is used to find type signatures for @quickCheck@able
     functions from Plutarch terms like @Term s (a :--> b :--> PBool)@.

 @since x.y.z
-}
type family TestableFun (p :: S -> Type) = r | r -> p where
    TestableFun PBool = TestableTerm PBool
    TestableFun (a :--> (b :: S -> Type)) = TestableTerm a -> (TestableFun b)

{- | Converts Plutarch Functions into `Testable` Haskell function of TestableTerms.

 @since x.y.z
-}
class FromPFunN (a :: S -> Type) (b :: S -> Type) where
    fromPFun :: (forall s. Term s (a :--> b)) -> TestableFun (a :--> b)

-- | @since x.y.z
instance {-# OVERLAPPING #-} FromPFunN a PBool where
    fromPFun f = \(TestableTerm x) -> TestableTerm $ f # x

-- | @since x.y.z
instance forall a b c d. (b ~ (c :--> d), FromPFunN c d) => FromPFunN a b where
    fromPFun f = \(TestableTerm x) -> fromPFun $ f # x

-- type family FromTestableFun (tp :: Type) where
--     FromTestableFun (TestableTerm p) = p
--     FromTestableFun (TestableTerm p -> ps) = p :--> FromTestableFun ps

-- class PTestableLam (a :: Type) (b :: Type) where
--     ptestableLam :: (a -> b) -> (forall s. Term s (FromTestableFun (a -> b)))

-- instance PTestableLam (TestableTerm a) (TestableTerm b) where
--     ptestableLam f' = undefined
--         where
--           -- f :: Term s (a :--> b)
--           -- f = plam' (\y -> let (TestableTerm x) = f' (TestableTerm y) in x)

--           test :: (forall s. Term s a) -> Term s b
--           test x = let (TestableTerm y) = f' $ TestableTerm $ x in y
        

{- | Extracts all @TestableTerm@s from give Plutarch function.

 @since x.y.z
-}
type family PLamArgs (p :: S -> Type) :: [Type] where
    PLamArgs (a :--> b) = TestableTerm a : (PLamArgs b)
    PLamArgs _ = '[]

{- | Make property by directly comparing behavior of Plutarch function
     to Haskell counterpart.  This function will expect all Plutarch
     types to be `plift`able and `pshow`able.  With given TestableTerm
     generator, it will generate value for each arguments. Then, it
     will apply generated value and lifted value to Plutarch and
     haskell function. Once all arguments are applied, It will check
     the equality of results.

 @since x.y.z
-}
class (PLamArgs p ~ args) => HaskEquiv (h :: Type) (p :: S -> Type) args where
    haskEquiv :: h -> TestableTerm p -> NP Gen args -> Property

instance
    forall ha hb pa pb hbArgs.
    ( PLamArgs pb ~ hbArgs
    , HaskEquiv hb pb hbArgs
    , PLifted pa ~ ha
    , PLift pa
    , PShow pa
    ) => HaskEquiv (ha -> hb) (pa :--> pb) (TestableTerm pa ': hbArgs) where
    haskEquiv h (TestableTerm p) (g :* gs) =
        forAll g $ \(TestableTerm x) -> haskEquiv (h $ plift x) (TestableTerm $ p # x) gs

instance (PLamArgs p ~ '[], PLift p, PLifted p ~ h, Eq h) => HaskEquiv h p '[] where
    haskEquiv h (TestableTerm p) _ = property $ plift p == h

{- | Simplified version of `haskEquiv`. It will use arbitrary instead of
     asking custom generators.

 @since x.y.z
-}
haskEquiv' ::
    forall h p args.
    ( PLamArgs p ~ args
    , HaskEquiv h p args
    , All Arbitrary args
    ) =>
    h -> (forall s. Term s p) -> Property
haskEquiv' h p = haskEquiv h (TestableTerm p) $ hcpure (Proxy @Arbitrary) arbitrary
    
-- | @since x.y.z
instance Testable (TestableTerm PBool) where
    property (TestableTerm t) = property (plift t)

{- | TestableTerm is a wrapper for closed Plutarch term. This
     abstraction allows Plutarch values can be generated via QuickCheck
     Generator.

     Hint: Typechecker is picky about how TestableTerm is constructed.
     Meaning, TestableTerm throw error when it's composed.

 @since x.y.z
-}
newtype TestableTerm a = TestableTerm (forall s. Term s a)

-- | @since x.y.z
liftTestable ::
    forall (a :: S -> Type) (b :: S -> Type).
    (forall (s :: S). Term s a -> Term s b) ->
    TestableTerm a ->
    TestableTerm b
liftTestable f (TestableTerm x) = TestableTerm $ f x

-- | @since x.y.z
lift2Testable ::
    forall (a :: S -> Type) (b :: S -> Type) (c :: S -> Type).
    (forall (s :: S). Term s a -> Term s b -> Term s c) ->
    TestableTerm a ->
    TestableTerm b ->
    TestableTerm c
lift2Testable f (TestableTerm x) (TestableTerm y) = TestableTerm $ f x y

-- | @since x.y.z
instance (forall (s :: S). Num (Term s a)) => Num (TestableTerm a) where
    (+) = lift2Testable (+)
    (*) = lift2Testable (*)
    abs = liftTestable abs
    negate = liftTestable negate
    signum = liftTestable signum
    fromInteger i = TestableTerm $ (fromInteger i :: Term s a)

-- | @since x.y.z
instance (forall (s :: S). Eq (Term s a)) => Eq (TestableTerm a) where
    (TestableTerm x) == (TestableTerm y) = x == y

{- | For any Plutarch Type that have `PShow` instance, `Show` is
     available as well. Unfortunately, for those that doesn't have
     @PShow@, `forAllShow` with custom show function is required to
     execute property check.

     This only works with those that have PShow instance; it may cause
     problems when dealing with Plutarch.Api datatypes which does not
     have PShow instances.

 @since x.y.z
-}
instance PShow a => Show (TestableTerm a) where
    show (TestableTerm term) =
        -- TODO: Possibly use HasCallStack (?)
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

    pshrink :: TestableTerm a -> [TestableTerm a]
    pshrink = const []

class PCoArbitrary (a :: S -> Type) where
    pcoarbitrary :: TestableTerm a -> Gen b -> Gen b

{- | Any Plutarch type that implements `PArbitrary a` automatically gets
     `Arbitrary` of @TestableTerm a@. This is an interfacing between
     QuickCheck and Plutarch.

 @since x.y.z
-}
instance PArbitrary p => Arbitrary (TestableTerm p) where
    arbitrary = parbitrary
    shrink = pshrink

instance PCoArbitrary p => CoArbitrary (TestableTerm p) where
    coarbitrary = pcoarbitrary

pdataT :: PIsData p => TestableTerm p -> TestableTerm (PAsData p)
pdataT (TestableTerm x) = TestableTerm $ pdata x

pfromDataT :: PIsData p => TestableTerm (PAsData p) -> TestableTerm p
pfromDataT (TestableTerm x) = TestableTerm $ pfromData x

pliftT :: (PLift p, PLifted p ~ h) => TestableTerm p -> h
pliftT (TestableTerm x) = plift x

pconstantT :: (PLift p, PLifted p ~ h) => h -> TestableTerm p
pconstantT h = TestableTerm $ pconstant h

pconT :: PCon p => (forall s. p s) -> TestableTerm p
pconT p = TestableTerm $ pcon p

pmatchT :: PMatch p => TestableTerm p -> (forall s. p s -> Term s b) -> TestableTerm b
pmatchT (TestableTerm p) f = TestableTerm $ pmatch p f

-- | @since x.y.z
instance (PArbitrary p, PIsData p) => PArbitrary (PAsData p) where
    parbitrary = do
        (TestableTerm x) <- parbitrary
        return $ TestableTerm $ pdata x
    pshrink = fmap pdataT . shrink . pfromDataT

instance (PCoArbitrary p, PIsData p) => PCoArbitrary (PAsData p) where
    pcoarbitrary (pfromDataT -> x) = pcoarbitrary x

instance Function (TestableTerm PInteger) where
    function = functionMap pliftT pconstantT

-- | @since x.y.z
instance PArbitrary PInteger where
    pshrink = fmap pconstantT . shrink . pliftT

instance PCoArbitrary PInteger where
    pcoarbitrary (pliftT -> x) = coarbitrary x

-- | @since x.y.z
instance PArbitrary PBool where
    pshrink = fmap pconstantT . shrink . pliftT

instance PCoArbitrary PBool where
    pcoarbitrary (pliftT -> x) = coarbitrary x    

-- | @since x.y.z
instance PArbitrary PUnit where
    pshrink = fmap pconstantT . shrink . pliftT

instance PCoArbitrary PUnit where
    pcoarbitrary (pliftT -> x) = coarbitrary x        

genByteStringUpto :: Int -> Gen ByteString
genByteStringUpto m = sized go
  where
    go :: Int -> Gen ByteString
    go s = chooseInt (0, min m s) >>= genByteString

genByteString :: Int -> Gen ByteString
genByteString l = Exts.fromList <$> vectorOf l arbitrary

shrinkByteString :: ByteString -> [ByteString]
shrinkByteString bs = do
  xs' <- shrink . Exts.toList $ bs
  pure . Exts.fromList $ xs'

-- | @since x.y.z
instance PArbitrary PByteString where
    parbitrary = do
        len <- chooseInt (0, 64)
        bs <- genByteString len
        return $ TestableTerm $ pconstant bs

    pshrink = fmap pconstantT . shrinkByteString . pliftT

instance PCoArbitrary PByteString where
    pcoarbitrary = coarbitrary . sum . Exts.toList . pliftT

-- | @since x.y.z
instance PArbitrary PRational where
    parbitrary = do
        (TestableTerm x) <- parbitrary
        (TestableTerm y) <- parbitrary
        return $ TestableTerm $ pcon $ PRational x y

    pshrink (TestableTerm x) =
        [ TestableTerm $ pcon $ PRational a b
        | (TestableTerm a) <- shrink (TestableTerm $ pnumerator # x)
        , (TestableTerm b) <- shrink (TestableTerm $ pdenominator # x)]

instance PCoArbitrary PRational where
    pcoarbitrary (TestableTerm x) = pcoarbitrary n . pcoarbitrary d
        where
          n = TestableTerm $ pnumerator # x
          d = TestableTerm $ pdenominator # x

-- | @since x.y.z
instance PArbitrary PString where
    parbitrary = (\x -> TestableTerm (pconstant (T.pack x))) <$> arbitrary
    pshrink = fmap (pconstantT . T.pack) . shrink . T.unpack . pliftT

instance PCoArbitrary PString where
    pcoarbitrary = coarbitrary . T.unpack . pliftT

-- | @since x.y.z
instance PArbitrary a => PArbitrary (PMaybe a) where
    parbitrary = do
        (TestableTerm x) <- parbitrary
        frequency [(3, return $ TestableTerm $ pcon $ PJust x), (1, return $ TestableTerm $ pcon $ PNothing)]
    pshrink (TestableTerm x)
        | plift $ pisJust # x =
          (TestableTerm $ pcon PNothing) :
          [ TestableTerm $ pcon $ PJust a
          | (TestableTerm a) <- shrink (TestableTerm $ pfromJust # x)
          ]
        | otherwise = []

instance PCoArbitrary a => PCoArbitrary (PMaybe a) where
    pcoarbitrary (TestableTerm x)
        | plift $ pisJust # x = variant 1 . (pcoarbitrary $ TestableTerm $ pfromJust # x)
        | otherwise = variant 0

-- | @since x.y.z
instance (PIsData a, PArbitrary a) => PArbitrary (PMaybeData a) where
    parbitrary = do
        (TestableTerm x) <- parbitrary
        elements $
            [ TestableTerm $ pcon $ PDJust $ pdcons @"_0" # (pdata x) # pdnil
            , TestableTerm $ pcon $ PDNothing pdnil
            ]
    pshrink (TestableTerm x)
        | plift $ pisDJust # x =
          (TestableTerm $ pcon $ PDNothing pdnil) :
          [ TestableTerm $ pcon $ PDJust $ pdcons @"_0" # (pdata a) # pdnil
          | (TestableTerm a) <- shrink (TestableTerm $ pfromDJust # x)
          ]
        | otherwise = []

instance (PIsData a, PCoArbitrary a) => PCoArbitrary (PMaybeData a) where
    pcoarbitrary (TestableTerm x)
        | plift $ pisDJust # x = variant 1 . (pcoarbitrary $ TestableTerm $ pfromDJust # x)
        | otherwise = variant 0

isRight = flip pmatchT $ \case
    PRight _ -> pconstant True
    _ -> pconstant False
pright = flip pmatchT $ \case
    PRight a -> a
    _ -> ptraceError "asked for PRight when it is PLeft"
pleft = flip pmatchT $ \case
    PLeft a -> a
    _ -> ptraceError "asked for PLeft when it is PRight"        

-- | @since x.y.z
instance (PArbitrary a, PArbitrary b) => PArbitrary (PEither a b) where
    parbitrary = do
        (TestableTerm x) <- parbitrary
        (TestableTerm y) <- parbitrary
        elements [TestableTerm $ pcon $ PRight x, TestableTerm $ pcon $ PLeft y]

    pshrink x
        | pliftT $ isRight x =
          [ pconT $ PRight a
          | (TestableTerm a) <- shrink (pright x)
          ]
        | otherwise =
          [ pconT $ PLeft a
          | (TestableTerm a) <- shrink (pleft x)
          ]          

instance (PCoArbitrary a, PCoArbitrary b) => PCoArbitrary (PEither a b) where
    pcoarbitrary x
        | pliftT $ isRight x = variant 0 . (pcoarbitrary $ pright x)
        | otherwise = variant 1 . (pcoarbitrary $ pleft x)
        
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

    pshrink = fmap pconstantT . shrink . pliftT

instance
    ( PLift a
    , PLift b
    , CoArbitrary (PLifted a, PLifted b)
    ) =>
    PCoArbitrary (PBuiltinPair a b) where
    pcoarbitrary = coarbitrary . pliftT

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

    pshrink = fmap fromTuple . shrink . toTuple
        where
          toTuple = liftTestable (pfromData . ptupleFromBuiltin . pdata)
          fromTuple = liftTestable (pfromData . pbuiltinPairFromTuple . pdata)

instance
    {-# OVERLAPPING #-}
    ( PCoArbitrary a
    , PCoArbitrary b
    , PIsData a
    , PIsData b
    ) =>
    PCoArbitrary (PBuiltinPair (PAsData a) (PAsData b)) where
    pcoarbitrary (liftTestable ptupleFromBuiltin . pdataT -> t) = pcoarbitrary t

ppFstT :: TestableTerm (PPair a b) -> TestableTerm a 
ppFstT = flip pmatchT $ \(PPair a _) -> a
ppSndT :: TestableTerm (PPair a b) -> TestableTerm b 
ppSndT = flip pmatchT $ \(PPair _ a) -> a    

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

    pshrink x =
        [ pconT $ PPair a b
        | (TestableTerm a) <- shrink $ ppFstT x
        , (TestableTerm b) <- shrink $ ppSndT x
        ]

instance (PCoArbitrary a, PCoArbitrary b) => PCoArbitrary (PPair a b) where
    pcoarbitrary x = pcoarbitrary (ppFstT x) . pcoarbitrary (ppSndT x)

ptFstT :: (PIsData a) => TestableTerm (PTuple a b) -> TestableTerm (PAsData a)
ptFstT = liftTestable $ (pfield @"_0" #)
ptSndT :: (PIsData b) => TestableTerm (PTuple a b) -> TestableTerm (PAsData b)
ptSndT = liftTestable $ (pfield @"_1" #)
        
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

    pshrink x = 
        [ TestableTerm $ ptuple # a # b
        | (TestableTerm a) <- shrink $ ptFstT x
        , (TestableTerm b) <- shrink $ ptSndT x
        ]    

instance
    ( PCoArbitrary a
    , PCoArbitrary b
    , PIsData a
    , PIsData b
    ) =>
    PCoArbitrary (PTuple a b) where
    pcoarbitrary x = pcoarbitrary (ptFstT x) . pcoarbitrary (ptSndT x)
    
psimplify :: (PLift a) => TestableTerm a -> TestableTerm a
psimplify (TestableTerm x) = TestableTerm $ pconstant $ plift x

constrPList :: (PIsListLike b a) => [TestableTerm a] -> TestableTerm (b a)
constrPList [] = TestableTerm $ pnil
constrPList ((TestableTerm x) : xs) =
    let (TestableTerm rest) = constrPList xs
    in TestableTerm $ pcons # x # rest

convToList :: (PIsListLike b a) => TestableTerm (b a) -> [TestableTerm a]
convToList (TestableTerm x)
    | not $ plift $ pnull # x = TestableTerm (phead # x) : convToList (TestableTerm $ ptail # x)
    | otherwise = []

genPListLike :: forall b a. (PArbitrary a, PIsListLike b a) => Gen (TestableTerm (b a))
genPListLike = constrPList <$> arbitrary

shrinkPListLike ::
    forall a b.
    ( PArbitrary a
    , PIsListLike b a
    ) =>
    TestableTerm (b a) ->
    [TestableTerm (b a)]
shrinkPListLike xs' = constrPList <$> shrink (convToList xs')

coArbitraryPListLike ::
    (PCoArbitrary a, PCoArbitrary (b a), PIsListLike b a) => TestableTerm (b a) -> Gen c -> Gen c 
coArbitraryPListLike (TestableTerm x)
    | plift (pnull # x) = variant 0
    | otherwise = variant 1 . (pcoarbitrary $ TestableTerm $ phead # x) . (pcoarbitrary $ TestableTerm $ ptail # x)

{-
This shinker "simplifies" underlaying plutarch representation. When
shrinking List, this shinker is always preferable.
-}
eshrinkPBIL ::
    forall a.
    ( PArbitrary a
    , PIsListLike PBuiltinList a
    , PLift a
    ) =>
    TestableTerm (PBuiltinList a) ->
    [TestableTerm (PBuiltinList a)]
eshrinkPBIL xs' = (psimplify . constrPList) <$> shrink (convToList xs')

-- | @since x.y.z
instance (PArbitrary a, PIsListLike PBuiltinList a) => PArbitrary (PBuiltinList a) where
    parbitrary = genPListLike
    pshrink = shrinkPListLike

instance (PCoArbitrary a, PIsListLike PBuiltinList a) => PCoArbitrary (PBuiltinList a) where
    pcoarbitrary = coArbitraryPListLike
        
-- | @since x.y.z
instance (PArbitrary a, PIsListLike PList a) => PArbitrary (PList a) where
    parbitrary = genPListLike
    pshrink = shrinkPListLike

instance (PCoArbitrary a, PIsListLike PList a) => PCoArbitrary (PList a) where
    pcoarbitrary = coArbitraryPListLike    

-- | @since x.y.z
instance (PArbitrary a, PIsListLike PStream a) => PArbitrary (PStream a) where
    parbitrary = genPListLike
    pshrink = shrinkPListLike

instance (PCoArbitrary a, PIsListLike PStream a) => PCoArbitrary (PStream a) where
    pcoarbitrary = coArbitraryPListLike        
    
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

    pshrink = fmap reMap . shrink . unMap
        where
          reMap (TestableTerm x) = pconT $ PMap x
          unMap = flip pmatchT $ \(PMap a) -> a

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

    pshrink = fmap (\(TestableTerm x) -> TestableTerm $ psort # (pcon $ PMap x)) . shrink . unMap
        where
          unMap = flip pmatchT $ \(PMap a) -> a

instance (PCoArbitrary a, PCoArbitrary b, PIsData a, PIsData b) => PCoArbitrary (PMap c a b) where
    pcoarbitrary = pcoarbitrary . unMap
        where
          unMap = flip pmatchT $ \(PMap a) -> a              

-- | @since x.y.z
instance PArbitrary PPOSIXTime where
    parbitrary = do
        (TestableTerm x) <- parbitrary
        return $ TestableTerm $ pcon $ PPOSIXTime x

    pshrink = fmap (\(TestableTerm x) -> pconT $ PPOSIXTime x) . shrink . unTime
        where
          unTime = flip pmatchT $ \(PPOSIXTime a) -> a

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

    pshrink = fmap (\(TestableTerm x) -> pconT $ PValue x) . shrink . unValue
        where
          unValue = flip pmatchT $ \(PValue a) -> a

-- | @since x.y.z
instance PArbitrary (PValue Unsorted NonZero) where
    parbitrary = do
        (TestableTerm val) <- parbitrary
        return $
            TestableTerm $
                pcon $
                    PValue $
                        Assoc.pmap # (plam $ \x -> Assoc.pfilter # (plam $ \y -> pnot # (y #== 0)) # x) # val

    pshrink = fmap reValue . shrink . unValue
        where
          unValue = flip pmatchT $ \(PValue a) -> a
          reValue (TestableTerm val) =
              pconT $ PValue $ Assoc.pmap # (plam $ \x -> Assoc.pfilter # (plam $ \y -> pnot # (y #== 0)) # x) # val

-- | @since x.y.z
instance PArbitrary (PValue Unsorted Positive) where
    parbitrary = do
        (TestableTerm val) <- parbitrary
        return $
            TestableTerm $
                pcon $
                    PValue $
                        Assoc.pmap # (plam $ \x -> Assoc.pfilter # (plam $ \y -> pnot # (0 #< y)) # x) # val

    pshrink = fmap reValue . shrink . unValue
        where
          unValue = flip pmatchT $ \(PValue a) -> a
          reValue (TestableTerm val) =
              pconT $ PValue $ Assoc.pmap # (plam $ \x -> Assoc.pfilter # (plam $ \y -> pnot # (0 #< y)) # x) # val

-- | @since x.y.z
instance PArbitrary (PValue Sorted NoGuarantees) where
    parbitrary = do
        (TestableTerm val) <- parbitrary
        return $ TestableTerm $ pcon $ PValue val

    pshrink = fmap (\(TestableTerm x) -> pconT $ PValue x) . shrink . unValue
        where
          unValue = flip pmatchT $ \(PValue a) -> a        

-- | @since x.y.z
instance PArbitrary (PValue Sorted NonZero) where
    parbitrary = do
        (TestableTerm val) <- parbitrary
        return $
            TestableTerm $
                Value.pnormalize
                    #$ pcon
                    $ PValue $
                        Assoc.pmap # (plam $ \x -> Assoc.pfilter # (plam $ \y -> pnot # (y #== 0)) # x) # val

    pshrink = fmap reValue . shrink . unValue
        where
          unValue = flip pmatchT $ \(PValue a) -> a
          reValue (TestableTerm val) =
              pconT $ PValue $ Assoc.pmap # (plam $ \x -> Assoc.pfilter # (plam $ \y -> pnot # (y #== 0)) # x) # val                        

-- | @since x.y.z
instance PArbitrary (PValue Sorted Positive) where
    parbitrary = do
        (TestableTerm val) <- (parbitrary :: Gen (TestableTerm (PValue Sorted NonZero)))
        return $
            TestableTerm $
                pcon $
                    PValue $
                        Assoc.pmap # (plam $ \x -> Assoc.pfilter # (plam $ \y -> (0 #<= y)) # x) # pto val

    pshrink = fmap reValue . shrink . unValue
        where
          unValue = flip pmatchT $ \(PValue a) -> a
          reValue (TestableTerm val) =
              pconT $ PValue $ Assoc.pmap # (plam $ \x -> Assoc.pfilter # (plam $ \y -> pnot # (0 #< y)) # x) # val                        
