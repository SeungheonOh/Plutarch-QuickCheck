{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ConstraintKinds #-}

module Function where

import Plutarch
import Plutarch.Prelude
import Plutarch.Lift
import Lib
import Data.Universe
import Test.QuickCheck.Function
import Test.QuickCheck
import Control.Arrow
import "liqwid-plutarch-extra" Plutarch.Extra.List
import Plutarch.Extra.Maybe
import Data.List
import Data.Kind

data PFun (a :: S -> Type) (b :: S -> Type) where
    PFun :: (PLift a, PLift b) =>
            [(PLifted a, PLifted b)] ->
            PLifted b ->
            (TestableTerm (a :--> b)) ->
            PFun a b

pattern PFn f <- (unTestableTerm . applyPFun -> f)

applyPFun :: (PLift a, PLift b) => PFun a b-> TestableTerm (a :--> b)
applyPFun (PFun _ _ f) = f

mkPFun :: forall (a :: S -> Type) (b :: S -> Type) (s :: S).
    ( PLift a
    , PLift b
    , PEq a
    ) =>
    [(PLifted a, PLifted b)] ->
    PLifted b ->
    PFun a b
mkPFun t d = PFun t d $ TestableTerm $ plamTable t d    

instance
    forall (a :: S -> Type) (b :: S -> Type) (s :: S).
    ( PLift a
    , PLift b
    , Arbitrary (PLifted a)
    , Arbitrary (PLifted b)
    , Eq (PLifted a)
    , PEq a
    ) =>
    Arbitrary (PFun a b) where
    arbitrary = do
        p <- arbitrary :: Gen [(PLifted a, PLifted b)]
        d <- arbitrary :: Gen (PLifted b)
        return $ mkPFun (nubBy (\x y -> fst x == fst y) p) d

    shrink (PFun t d _) =
        [mkPFun t' d' | (t', d') <- shrink (t, d)]

instance
    forall (a :: S -> Type) (b :: S -> Type) (s :: S).
    ( PLift a
    , PLift b
    , Show (PLifted a)
    , Show (PLifted b)
    ) =>
    Show (PFun a b) where
    show = showPFun

showPFun ::
    forall (a :: S -> Type) (b :: S -> Type) (s :: S).
    ( PLift a
    , PLift b
    , Show (PLifted a)
    , Show (PLifted b)
    ) =>
    PFun a b-> String
showPFun (PFun t d _) =
    "{\n" ++
    intercalate ", \n" (
    [ show x ++ " -> " ++ show c
    | (x, c) <- t
    ] ++
    ["_ -> " ++ show d])
    ++ "\n}"

plamTable ::
    forall (a :: S -> Type) (b :: S -> Type) (s :: S).
    ( PLift a
    , PLift b
    , PEq a
    ) =>
    [(PLifted a, PLifted b)] ->
    PLifted b ->
    Term s (a :--> b)
plamTable t d = plam $ \x -> pmaybe # pconstant d # (plookup # x # pconstant t)

pfiniteFunction ::
    forall (a :: S -> Type) (b :: S -> Type) (s :: S).
    ( Finite (PLifted a)
    , PLift a
    , PLift b
    , PEq a
    ) =>
    (PLifted a -> PLifted b) ->
    Term s (a :--> b)
pfiniteFunction f = plam $ \x -> pfromJust #$ plookup # x # table
    where
      table :: Term s (PBuiltinList (PBuiltinPair a b))
      table = pconstant $ (id &&& f) <$> universeF

-- pfiniteFunction2 ::
--     forall (a :: S -> Type) (b :: S -> Type) (c :: S -> Type) (s :: S).
--     ( Finite (PLifted a)
--     , PLift a
--     , PLift b
--     , PLift c
--     , PEq a
--     ) =>
--     (PLifted a -> PLifted b -> PLifted c) ->
--     Term s (a :--> b :--> c)
-- pfiniteFunction2 f = plam $ \x -> pfromJust #$ plookup # x # table
--     where
--       table :: Term s (PBuiltinList (PBuiltinPair a b))
--       table = pconstant $ (id &&& f) <$> universeF

-- instance Functor ((:=>) a) where
--   fmap f (Unit c)    = Unit (f c)
--   fmap f Nil         = Nil
--   fmap f (Map g h p) = Map g h (fmap f p)

-- abstract :: (a :=> c) -> c -> (a -> c)
-- abstract (Unit c)    _ _     = c
-- abstract Nil         d _     = d
-- abstract (Map g _ p) d x     = abstract p d (g x)

-- applyPFun :: (PLift a, PLift b) => Fun (PLifted a) (PLifted b) -> Term s (a :--> b)
-- applyPFun (Fun (t, d) _) = undefined      

-- liftedTest :: Term s (PInteger :--> PInteger)
-- liftedTest = plam $ \x -> pconstant $ test (plift x)

--    plamT $ \x -> unTestableTerm $ abstract p d (g (TestableTerm x))
-- pabstract _ _ = undefined

-- pabstract :: (Term s a :=> Term s c) -> Term s c -> Term s (a :--> c)
-- pabstract Nil d = plam $ const d
-- pabstract (Unit c) _ = plam $ const c
-- pabstract (Table xys) d = plam $ \x -> head ([y | (x',y) <- xys, x == x'] ++ [d])
-- --pabstract (p :+: q)   d = either (abstract p d) (abstract q d)
-- pabstract (Map g _ p) d = plam $ \x -> abstract p d (g x)
-- --pabstract _ _ = error "Pair and :+: is not supported"

-- pabstract :: PPartial a c s -> Term s c -> Term s (a :--> c)
-- pabstract (PPartial Nil) d = plam $ const d
-- pabstract (PPartial (Unit c)) _ = plam $ const c
-- -- pabstract (PTable xys) d = plam $ \x ->
-- --     head ([y | (x',y) <- xys, pliftT (TestableTerm (x #== unTestableTerm x'))] ++ [d])
-- pabstract (PPartial (Map g _ p)) d = plam $ \x -> abstract p d (g x)

-- test :: Term s PInteger :=> Term s PBool --[(Term s PInteger, Term s PBool)]
-- test = Table [(pconstant 5, pconstant False)]

-- plamT :: (Term s a -> TestableTerm b) -> TestableTerm (a :--> b)
-- plamT f = TestableTerm $ plam $ (\x -> unTestableTerm $ f x)

-- instance (Show a, Show b) => Show (a:=>b) where
--   show p = showFunction p Nothing

-- only use this on finite functions
-- showFunction :: (Show a, Show b) => (a :=> b) -> Maybe b -> String
-- showFunction p md =
--   "{" ++ concat (intersperse ", " ( [ show x ++ "->" ++ show c
--                                     | (x,c) <- table p
--                                     ]
--                                  ++ [ "_->" ++ show d
--                                     | Just d <- [md]
--                                     ] )) ++ "}"
  -- 

-- data PFun a b= 
--     PFun (TestableTerm a :=> TestableTerm b, TestableTerm b, Bool) (TestableTerm (a :--> b))

pappT :: TestableTerm (a :--> b) -> TestableTerm a -> TestableTerm b
pappT (TestableTerm f) (TestableTerm x) = TestableTerm $ f # x

-- composeT :: TestableTerm (b :--> c) -> TestableTerm (a :--> b) -> TestableTerm (a :--> c)
-- composeT (TestableTerm g) (TestableTerm f) = TestableTerm $ plam $ \x -> g #$ f # x

-- -- mapPFun :: TestableTerm (b :--> c) -> PFun a b -> PFun a c
-- -- mapPFun f'@(haskellPFun -> f) (PFun (p, d, s) g) = PFun ((fmap f p), f d, s) (composeT f' g)

