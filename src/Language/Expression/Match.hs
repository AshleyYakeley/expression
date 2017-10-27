{-# OPTIONS -Wno-redundant-constraints #-}
module Language.Expression.Match where
{
    import Import;
    import Language.Expression.Expression;


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
}
