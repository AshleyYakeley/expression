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

    valueSymbolMap :: (Functor f) =>
     MapWitness (Dual (->)) wit1 wit2 -> ValueExpression wit1 f r -> ValueExpression wit2 f r;
    valueSymbolMap mapwit (MkExpression wits fcvr) = case mapList mapwit wits of
    {
        MkMapList wits' (Dual mapvals) -> MkExpression wits' (fmap (\valsr -> valsr . mapvals) fcvr);
    };

    valueSymbol :: (Applicative f) => wit val -> ValueExpression wit f val;
    valueSymbol = expressionSymbol (pure (\(val,()) -> val));

    abstract :: (TestEquality wit,Functor f) => wit val -> ValueExpression wit f r -> ValueExpression wit f (val -> r);
    abstract wit (MkExpression wits fvsr) = case removeAllMatching wit wits of
    {
        MkRemoveFromList newwits ins _rem -> MkExpression newwits (fmap (\vsr vals a -> vsr (ins a vals)) fvsr);
    };

    letBind :: (TestEquality wit,Applicative f) => wit val -> ValueExpression wit f val -> ValueExpression wit f r -> ValueExpression wit f r;
    letBind wit valExp exp = (abstract wit exp) <*> valExp;

    evaluateExpression :: (Applicative m,Functor f) => (forall val. wit val -> m val) -> ValueExpression wit f r -> m (f r);
    evaluateExpression resolve (MkExpression wits fvr) =
     fmap (\vals -> fmap (\vr -> vr vals) fvr) (listSequence (listTypeMap resolve wits));

    matchBind :: (TestEquality wit,Functor f1,Functor f2) =>
        MatchExpression wit f1 a ->
        ValueExpression wit f2 b ->
        ValueExpression wit (Compose f1 f2) (a,b);
    matchBind (MkExpression matchWits f1vca) (MkExpression valueWits f2vtb) = case removeAllMatchingMany matchWits valueWits of
    {
        MkRemoveManyFromList newValueWits insM _remM -> MkExpression newValueWits
         (Compose (fmap (\(lx,a) -> fmap (\lb lr -> (a,lb (insM lx lr))) f2vtb) f1vca));
    };

    matchSimple :: (Functor f) => f r -> MatchExpression wit f r;
    matchSimple fr = MkExpression NilListType (fmap (\r -> ((),r)) fr);

    matchBoth :: (TestEquality wit,Applicative f) => MatchExpression wit f () -> MatchExpression wit f () -> MatchExpression wit f ();
    matchBoth = liftA2 (\_ _ -> ());

    matchAll :: (TestEquality wit,Applicative f) => [MatchExpression wit f ()] -> MatchExpression wit f ();
    matchAll [] = pure ();
    matchAll (exp:exps) = matchBoth exp (matchAll exps);

    matchSymbolMap :: (Functor f) =>
     MapWitness (->) wit1 wit2 -> MatchExpression wit1 f r -> MatchExpression wit2 f r;
    matchSymbolMap mapwit (MkExpression wits fcvr) = case mapList mapwit wits of
    {
        MkMapList wits' mapvals -> MkExpression wits' (fmap (\(vals,r) -> (mapvals vals,r)) fcvr);
    };

    toSimpleValueExpression :: (Functor f) =>
     ValueExpression wit f r -> ValueExpression wit Identity (f r);
    toSimpleValueExpression (MkExpression vwits fvsr) = MkExpression vwits (Identity (\vals -> fmap (\vsr -> vsr vals) fvsr));

    type PatternExpression wit ff q = MatchExpression wit (Compose ((->) q) ff);

    pattern :: (Functor ff) => (q -> ff r) -> PatternExpression wit ff q r;
    pattern qmr = matchSimple (Compose qmr);

    patternExpressionJoin :: (TestEquality wit) =>
     (forall v1 v2 v3. MergeValList wit v1 v2 v3 -> (q1 -> ff1 (v1,r1)) -> (q2 -> ff2 (v2,r2)) -> (q3 -> ff3 (v3,r3))) ->
     PatternExpression wit ff1 q1 r1 -> PatternExpression wit ff2 q2 r2 -> PatternExpression wit ff3 q3 r3;
    patternExpressionJoin f = expressionJoin (\mvl (Compose qffvr1) (Compose qffvr2) -> Compose (f mvl qffvr1 qffvr2));

    patternBoth :: (TestEquality wit,Applicative ff) =>
     PatternExpression wit ff q r1 -> PatternExpression wit ff q r2 -> PatternExpression wit ff q (r1,r2);
    patternBoth = patternExpressionJoin (\mvl qffvr1 qffvr2 q ->
      liftA2 (\(v1,r1) (v2,r2) -> (mergeValList mvl (\_ v _ -> v) v1 v2,(r1,r2))) (qffvr1 q) (qffvr2 q)
    );

    patternFilter :: (Monad ff) => (q -> a -> ff b) -> PatternExpression wit ff q a -> PatternExpression wit ff q b;
    patternFilter qaffb (MkExpression wits (Compose qffva)) =
     MkExpression wits (Compose (\q -> do
        {
            (v,a) <- qffva q;
            b <- qaffb q a;
            return (v,b);
        }));

    patternNever :: (MonadPlus ff,Applicative ff) => PatternExpression wit ff q r;
    patternNever = pattern (\_ -> mzero);

    patternMapFunctor :: (forall a. ff1 a -> ff2 a) -> PatternExpression wit ff1 q r -> PatternExpression wit ff2 q r;
    patternMapFunctor ff = expressionMapFunctor (\(Compose qffa) -> Compose (fmap ff qffa));

{-
    expressionSymbol :: (q -> ff ((val,()),r)) -> wit val -> PatternExpression wit ff q r;
    expressionSymbol' :: (q -> ff (val,r)) -> wit val -> PatternExpression wit ff q r;
    expressionSymbol fcvr wit = MkExpression (ConsListType wit NilListType) (Compose fcvr);

    patternAddSymbol :: (Applicative ff) => wit val -> PatternExpression wit ff val r -> PatternExpression wit ff val r;
    patternAddSymbol = expressionSymbol (Compose (\val -> pure ((val,()),())));
-}
    patternSymbol :: (Applicative ff) => wit val -> PatternExpression wit ff val ();
    patternSymbol = expressionSymbol (Compose (\val -> pure ((val,()),())));

    patternMatch :: (MonadPlus ff,Applicative ff) => (q -> Bool) -> PatternExpression wit ff q ();
    patternMatch qb = pattern (\q -> if qb q then return () else mzero);

    patternMatchEq :: (MonadPlus ff,Applicative ff,Eq q) => q -> PatternExpression wit ff q ();
    patternMatchEq q = patternMatch ((==) q);
{-
    mapList :: (forall r v1. w1 v1 -> (forall v2. w2 v2 -> (v1 -> v2) -> r) -> r) -> ListType w1 l -> MapList w1 w2 l;
-}

    composePattern :: (TestEquality wit,Monad ff) =>
     PatternExpression wit ff q r -> PatternExpression wit ff p q -> PatternExpression wit ff p r;
    composePattern = patternExpressionJoin (\mvl qmv1r pmv2q p -> do
    {
        (vals2,q) <- pmv2q p;
        (vals1,r) <- qmv1r q;
        return (mergeValList mvl (\_ v _ -> v) vals1 vals2,r);
    });

    subPattern :: (TestEquality wit,Monad ff,Applicative ff) =>
     (q -> ff p) -> PatternExpression wit ff p r -> PatternExpression wit ff q r;
    subPattern qmp patp = composePattern patp (pattern qmp);

    patternMatchPair :: (TestEquality wit,Monad ff,Applicative ff) =>
     PatternExpression wit ff p () -> PatternExpression wit ff q () -> PatternExpression wit ff (p,q) ();
    patternMatchPair patp patq = matchBoth (subPattern (return . fst) patp) (subPattern (return . snd) patq);
}
