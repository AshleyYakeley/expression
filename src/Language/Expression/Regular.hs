module Language.Expression.Regular where
{
    import Import;
    import Prelude(undefined);
    import Language.Expression.Expression;

    type RegularExpression wit t = PatternExpression wit [] t t;

    regexSet :: (c -> Bool) -> RegularExpression wit [c];
    regexSet set = pattern (\s -> case s of
    {
        (c:cs) | set c -> [cs];
        _ -> [];
    });

    regexEmpty :: RegularExpression wit t;
    regexEmpty = pattern (\s -> [s]);

    regexConcat :: (forall val. wit val -> val -> val -> val) -> RegularExpression wit t -> RegularExpression wit t -> RegularExpression wit t;
    regexConcat = undefined;

    regexAlternate :: (forall val. wit val -> Maybe val -> val) -> RegularExpression wit t -> RegularExpression wit t -> RegularExpression wit t;
    regexAlternate = undefined;

    regexStar :: (forall val. wit val -> val) -> (forall val. wit val -> val -> val -> val) -> RegularExpression wit t -> RegularExpression wit t;
    regexStar vnil vcons r = regexAlternate (\wit mval -> case mval of
    {
        Nothing -> vnil wit;
        Just val -> val;
    }) (regexConcat vcons r (regexStar vnil vcons r)) regexEmpty;

    regexParallel :: RegularExpression wit t -> RegularExpression wit t -> RegularExpression wit t;
    regexParallel = undefined;

    regexImpossible :: RegularExpression wit t;
    regexImpossible = patternNever;

    regexAnything :: RegularExpression wit t;
    regexAnything = undefined;

    regexSymbol :: (t -> val) -> wit val -> RegularExpression wit t;
    regexSymbol = undefined;

    regexAnyChar :: RegularExpression wit [c];
    regexAnyChar = pattern (\s -> case s of
    {
        (_:cs) -> [cs];
        _ -> [];
    });
}
