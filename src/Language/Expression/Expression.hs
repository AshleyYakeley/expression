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
        (MkExpression wits1 fcvab) <*> (MkExpression wits2 fcva) = case witnessedListAppend wits1 wits2 of
        {
            Dict -> MkExpression (listAppendWitness wits1 wits2) (liftA2 (\v1ab v2a v12 -> case listSplit v12 of
            {
                (v1,v2) -> (v1ab v1) (v2a v2);
            }) fcvab fcva);
        }
    };

    instance (Applicative f) => Applicative (MatchExpression wit f) where
    {
        pure a = MkExpression NilListType (pure (pure a));
        (MkExpression wits1 fcvab) <*> (MkExpression wits2 fcva) = case witnessedListAppend wits1 wits2 of
        {
            Dict -> MkExpression (listAppendWitness wits1 wits2) (liftA2 (\(v1,ab) (v2,a) -> (listJoin v1 v2,ab a)) fcvab fcva);
        }
    };

    valueSymbolMap :: (Functor f) =>
     MapWitness (Dual (->)) wit1 wit2 -> ValueExpression wit1 f r -> ValueExpression wit2 f r;
    valueSymbolMap mapwit (MkExpression wits fcvr) = case mapList mapwit wits of
    {
        MkMapList wits' (Dual mapvals) -> MkExpression wits' (fmap (\valsr -> valsr . mapvals) fcvr);
    };

    valueSymbol :: (Applicative f) => wit val -> ValueExpression wit f val;
    valueSymbol = expressionSymbol (pure (\(val,()) -> val));

    abstract :: (SimpleWitness wit,Functor f) => wit val -> ValueExpression wit f r -> ValueExpression wit f (val -> r);
    abstract wit (MkExpression wits fvsr) = case removeAllMatching wit wits of
    {
        MkRemoveFromList newwits ins _rem -> MkExpression newwits (fmap (\vsr vals a -> vsr (ins a vals)) fvsr);
    };

    letBind :: (SimpleWitness wit,Applicative f) => wit val -> ValueExpression wit f val -> ValueExpression wit f r -> ValueExpression wit f r;
    letBind wit valExp exp = (abstract wit exp) <*> valExp;

    evaluateExpression :: (Applicative m,Functor f) => (forall val. wit val -> m val) -> ValueExpression wit f r -> m (f r);
    evaluateExpression resolve (MkExpression wits fvr) =
     fmap (\vals -> fmap (\vr -> vr vals) fvr) (listSequence (listTypeMap resolve wits));

    matchBind :: (SimpleWitness wit,Functor f1,Functor f2) =>
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

    matchBoth :: (Applicative f) => MatchExpression wit f () -> MatchExpression wit f () -> MatchExpression wit f ();
    matchBoth = liftA2 (\_ _ -> ());

    matchAll :: (Applicative f) => [MatchExpression wit f ()] -> MatchExpression wit f ();
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

    patternNever :: (MonadPlus ff,Applicative ff) => PatternExpression wit ff q r;
    patternNever = pattern (\_ -> mzero);
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

    composePattern :: (Monad ff) =>
     PatternExpression wit ff q r -> PatternExpression wit ff p q -> PatternExpression wit ff p r;
    composePattern (MkExpression wits1 (Compose qmv1r)) (MkExpression wits2 (Compose pmv2q)) =
     case witnessedListAppend wits1 wits2 of
    {
        Dict -> MkExpression (listAppendWitness wits1 wits2) (Compose (\p -> do
        {
            (vals2,q) <- pmv2q p;
            (vals1,r) <- qmv1r q;
            return (listJoin vals1 vals2,r);
        }));
    };

    subPattern :: (Monad ff,Applicative ff) =>
     (q -> ff p) -> PatternExpression wit ff p r -> PatternExpression wit ff q r;
    subPattern qmp patp = composePattern patp (pattern qmp);

    patternMatchPair :: (Monad ff,Applicative ff) =>
     PatternExpression wit ff p () -> PatternExpression wit ff q () -> PatternExpression wit ff (p,q) ();
    patternMatchPair patp patq = matchBoth (subPattern (return . fst) patp) (subPattern (return . snd) patq);
}
