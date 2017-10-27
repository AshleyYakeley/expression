module Language.Expression.Mono where
{
    import Import;
    import Language.Expression.Expression;
    import Language.Expression.Value;
    import Language.Expression.Match;
    import Language.Expression.Pattern;
    import Language.Expression.Regular;


    -- monomorphic symbols, representing type val

    data MonoSymbol (sym :: *) (val :: *) (val' :: *) where
    {
        MkMonoSymbol :: sym -> MonoSymbol sym val val;
    };

    instance (Eq sym) => TestEquality (MonoSymbol sym val) where
    {
        testEquality (MkMonoSymbol sym1) (MkMonoSymbol sym2) | sym1 == sym2 = Just Refl;
        testEquality _ _ = Nothing;
    };

    type MonoValueExpression sym val = ValueExpression (MonoSymbol sym val);
    type MonoPatternExpression sym val ff q = PatternExpression (MonoSymbol sym val) ff q;
    type MonoRegularExpression sym val t = RegularExpression (MonoSymbol sym val) t;

    monoWitMap :: (sym1 -> sym2) ->
     Expression combine (MonoSymbol sym1 val) f r -> Expression combine (MonoSymbol sym2 val) f r;
    monoWitMap ss = witMap (\(MkMonoSymbol sym1) -> MkMonoSymbol (ss sym1));

    monoValueSymbol :: (Applicative f) => sym -> MonoValueExpression sym val f val;
    monoValueSymbol sym = valueSymbol (MkMonoSymbol sym);

    monoPatternSymbol :: (Applicative ff) => sym -> MonoPatternExpression sym val ff val ();
    monoPatternSymbol sym = patternSymbol (MkMonoSymbol sym);
{-
    monoPatternSymbolMap :: (val1 -> val2) -> MonoPatternExpression sym val1 ff q r -> MonoPatternExpression sym val2 ff q r;
    monoPatternSymbolMap
-}
    monoLetBind :: (Eq sym,Applicative f) =>
     sym -> MonoValueExpression sym val f val -> MonoValueExpression sym val f r -> MonoValueExpression sym val f r;
    monoLetBind sym = letBind (MkMonoSymbol sym);

    monoPatternBind :: (Eq sym,Applicative f,Functor ff) =>
        MonoPatternExpression sym val ff q () ->
        MonoValueExpression sym val f r ->
        MonoValueExpression sym val (Compose (Compose ((->) q) ff) f) r;
    monoPatternBind patExp valExp = fmap snd (matchBind patExp valExp);

    monoEvaluateExpression :: (Applicative m,Functor f) => (sym -> m val) -> MonoValueExpression sym val f r -> m (f r);
    monoEvaluateExpression smv = evaluateExpression (\(MkMonoSymbol sym) -> smv sym);
}
