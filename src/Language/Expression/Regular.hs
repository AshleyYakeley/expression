module Language.Expression.Regular where
{
    import Import;
    import Data.List(length,take,drop,(++));
    import Prelude(undefined,Int,Num(..),Ord(..));
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
        nullv1 = listFill (valListWit1 mvl) nullValue;
        nullv2 = listFill (valListWit2 mvl) nullValue;
        m1 = fmap (\(v1,l1) -> (vmap v1 nullv2,l1)) matches1;
        m2 = fmap (\(v2,l1) -> (vmap nullv1 v2,l1)) matches2
    } in m1 ++ m2);

    regexRepeat :: (SimpleWitness wit) =>
    Int -> Maybe Int ->
    (forall val. wit val -> val) -> (forall val. wit val -> val -> val -> val) ->
    RegularExpression wit [c] -> RegularExpression wit [c];
    regexRepeat min' mmax' vnil vcons (MkExpression wits (Compose tlvi)) = MkExpression wits (Compose (let
    {
        matchEmpty = return (listFill wits vnil,0);

        matchOne th t = do
        {
            (va,i) <- tlvi t;
            (vrest,i') <- th (drop i t);
            return (listLift2 wits vcons va vrest,i + i');
        };

        thing 0 (Just 0) _t = matchEmpty;
        thing 0 (Just n) _t | n < 0 = mzero;
        thing 0 (Just n) t = mplus (matchOne (thing 0 (Just (n - 1))) t) matchEmpty;
        thing 0 Nothing t = mplus (matchOne (thing 0 Nothing) t) matchEmpty;
        thing minr mextra t = matchOne (thing (minr - 1) mextra) t;
    } in thing min' (fmap (\max' -> max' - min') mmax')));

    -- regexAlternate vnil (regexConcat vcons r (regexStar vnil vcons r)) regexEmpty;

    regexParallel :: (SimpleWitness wit,Eq t) => RegularExpression wit t -> RegularExpression wit t -> RegularExpression wit t;
    regexParallel r1 r2 = patternFilter (\_ (t1,t2) -> if t1 == t2 then [t1] else []) (patternBoth r1 r2);

    regexImpossible :: RegularExpression wit t;
    regexImpossible = patternNever;

    regexAnything :: RegularExpression wit [c];
    regexAnything = pattern (\t -> allCounts (length t)) where
    {
        allCounts 0 = [0];
        allCounts n = n:(allCounts (n - 1));
    };

    regexSymbol :: ([c] -> val) -> wit val -> RegularExpression wit [c] -> RegularExpression wit [c];
    regexSymbol toval wit (MkExpression wits (Compose tlvi)) = MkExpression (ConsListType wit wits) (Compose (\t ->
        fmap (\(v,i) -> ((toval (take i t),v),i)) (tlvi t)
    ));

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

    regexAll :: RegularExpression wit [c] -> PatternExpression wit [] [c] ();
    regexAll = patternFilter (\t a -> if a == length t then [()] else []);

    firstItem :: [a] -> Maybe a;
    firstItem (a:_) = Just a;
    firstItem [] = Nothing;

    regexSingle :: RegularExpression wit [c] -> PatternExpression wit Maybe [c] ();
    regexSingle = patternMapFunctor firstItem . regexAll;
}
