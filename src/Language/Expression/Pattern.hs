{-# OPTIONS -Wno-redundant-constraints #-}
module Language.Expression.Pattern where
{
    import Import;
    import Language.Expression.Expression;
    import Language.Expression.Match;


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
