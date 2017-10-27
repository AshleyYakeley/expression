{-# OPTIONS -Wno-redundant-constraints #-}
module Language.Expression.Value where
{
    import Import;
    import Language.Expression.Expression;


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

    toSimpleValueExpression :: (Functor f) =>
     ValueExpression wit f r -> ValueExpression wit Identity (f r);
    toSimpleValueExpression (MkExpression vwits fvsr) = MkExpression vwits (Identity (\vals -> fmap (\vsr -> vsr vals) fvsr));
}
