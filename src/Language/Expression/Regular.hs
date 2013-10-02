module Language.Expression.Regular where
{
    import Import;
    import Data.List(length,drop,(++));
    import Prelude(undefined,Int,Num(..));
    import Language.Expression.Expression;

    type RegularExpression wit t = PatternExpression wit [] t Int;

    startsWith :: (Eq a) => [a] -> [a] -> Bool;
    startsWith [] _ = True;
    startsWith (a:aa) (b:bb) | a == b = startsWith aa bb;
    startsWith _ _ = False;

    regexSet :: (c -> Bool) -> RegularExpression wit [c];
    regexSet set = pattern (\s -> case s of
    {
        (c:_) | set c -> [1];
        _ -> [];
    });

    regexEmpty :: RegularExpression wit t;
    regexEmpty = pattern (\_ -> [0]);
{-
    patternExpressionJoin ::
     (forall v. wit v -> v -> v -> v) ->
     (forall v1 v2 v3. (v1 -> v2 -> v3) -> (t -> [(v1,Int)]) -> (t -> [(v2,Int)]) -> (t -> [(v3,Int)])) ->
     RegularExpression wit t -> RegularExpression wit t -> RegularExpression wit t;
-}

    regexConcat :: (SimpleWitness wit) =>
     (forall val. wit val -> val -> val -> val) -> RegularExpression wit [c] -> RegularExpression wit [c] -> RegularExpression wit [c];
    regexConcat pickVal = patternExpressionJoin (\mvl exp1 exp2 t -> do
    {
        (v1,l1) <- exp1 t;
        (v2,l2) <- exp2 (drop l1 t);
        return (mergeValList mvl pickVal v1 v2,l1 + l2);
    });

    regexAlternate :: (SimpleWitness wit) =>
     (forall val. wit val -> val) -> RegularExpression wit t -> RegularExpression wit t -> RegularExpression wit t;
    regexAlternate nullValue = patternExpressionJoin (\mvl exp1 exp2 t -> let
    {
        vmap = mergeValList mvl (\_ v _ -> v);
        matches1 = exp1 t;
        matches2 = exp2 t;
        nullv1 = listFill nullValue (valListWit1 mvl);
        nullv2 = listFill nullValue (valListWit2 mvl);
        m1 = fmap (\(v1,l1) -> (vmap v1 nullv2,l1)) matches1;
        m2 = fmap (\(v2,l1) -> (vmap nullv1 v2,l1)) matches2
    } in m1 ++ m2);

    regexStar :: (SimpleWitness wit) =>
    (forall val. wit val -> val) -> (forall val. wit val -> val -> val -> val) -> RegularExpression wit [c] -> RegularExpression wit [c];
    regexStar vnil vcons r = regexAlternate vnil (regexConcat vcons r (regexStar vnil vcons r)) regexEmpty;

    regexParallel :: (SimpleWitness wit,Eq t) => RegularExpression wit t -> RegularExpression wit t -> RegularExpression wit t;
    regexParallel r1 r2 = patternFilter (\(t1,t2) -> if t1 == t2 then [t1] else []) (patternBoth r1 r2);

    regexImpossible :: RegularExpression wit t;
    regexImpossible = patternNever;
{-
    regexAnything :: RegularExpression wit t;
    regexAnything = undefined;
-}
    regexSymbol :: (t -> val) -> wit val -> RegularExpression wit t;
    regexSymbol = undefined;

    regexText :: (Eq c) => [c] -> RegularExpression wit [c];
    regexText text = pattern (\s -> case startsWith text s of
    {
        True -> [length text];
        False -> [];
    });

    regexAnyChar :: RegularExpression wit [c];
    regexAnyChar = pattern (\s -> case s of
    {
        (_:_) -> [1];
        _ -> [];
    });
}
