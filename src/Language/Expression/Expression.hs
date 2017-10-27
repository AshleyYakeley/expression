{-# OPTIONS -Wno-redundant-constraints #-}
module Language.Expression.Expression where
{
    import Import;

    data Expression (combine :: * -> * -> *) (wit :: * -> *) (f :: * -> *) (r :: *) where
    {
        MkExpression :: ListType wit vals -> f (combine vals r) -> Expression combine wit f r;
    };

    expressionSymbol :: f (combine (val,()) r) -> wit val -> Expression combine wit f r;
    expressionSymbol fcvr wit = MkExpression (ConsListType wit NilListType) fcvr;

    witMap :: (forall a. wit1 a -> wit2 a) -> Expression combine wit1 f r -> Expression combine wit2 f r;
    witMap ww (MkExpression wits fcvr) = MkExpression (listTypeMap ww wits) fcvr;

    data MergeValList wit v1 v2 v3 = MkMergeValList
    {
        valListWit1 :: ListType wit v1,
        valListWit2 :: ListType wit v2,
        valListWit3 :: ListType wit v3,
        mergeValList :: (forall t. wit t -> t -> t -> t) -> v1 -> v2 -> v3,
        unmergeValList :: v3 -> (v1,v2)
    };

    expressionMapFunctor :: (forall a. f1 a -> f2 a) -> Expression combine wit f1 r -> Expression combine wit f2 r;
    expressionMapFunctor ff (MkExpression wits f1cvr) = MkExpression wits (ff f1cvr);

    expressionJoin :: (TestEquality wit) =>
     (forall v1 v2 v3. MergeValList wit v1 v2 v3 -> f1 (combine v1 r1) -> f2 (combine v2 r2) -> f3 (combine v3 r3)) ->
     Expression combine wit f1 r1 -> Expression combine wit f2 r2 -> Expression combine wit f3 r3;
    expressionJoin f (MkExpression wits1 f1vr1) (MkExpression wits2 f2vr2) = case mergeList wits1 wits2 of
    {
        MkMergeList wits3 merge unmerge -> MkExpression wits3 (f (MkMergeValList
        {
            valListWit1 = wits1,
            valListWit2 = wits2,
            valListWit3 = wits3,
            mergeValList = merge,
            unmergeValList = unmerge
        }) f1vr1 f2vr2);
    };

    type ValueExpression = Expression (->);
    type MatchExpression = Expression (,);

    instance (Functor f) => Functor (ValueExpression wit f) where
    {
        fmap ab (MkExpression wits fcva) = MkExpression wits (fmap (fmap ab) fcva);
    };

    instance (Functor f) => Functor (MatchExpression wit f) where
    {
        fmap ab (MkExpression wits fcva) = MkExpression wits (fmap (fmap ab) fcva);
    };

    instance (Applicative f) => Applicative (ValueExpression wit f) where
    {
        pure a = MkExpression NilListType (pure (pure a));
        (MkExpression wits1 fcvab) <*> (MkExpression wits2 fcva) = case appendList wits1 wits2 of
        {
            MkAppendList wit _join split -> MkExpression wit (liftA2 (\v1ab v2a v12 -> case split v12 of
            {
                (v1,v2) -> (v1ab v1) (v2a v2);
            }) fcvab fcva);
        }
    };

    instance (TestEquality wit,Applicative f) => Applicative (MatchExpression wit f) where
    {
        pure a = MkExpression NilListType (pure (pure a));
        (<*>) = expressionJoin (\mvl fcvab fcva -> liftA2 (\(v1,ab) (v2,a) -> (mergeValList mvl (\_ v _ -> v) v1 v2,ab a)) fcvab fcva);
    };
}
