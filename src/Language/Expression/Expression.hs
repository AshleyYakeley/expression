module Language.Expression.Expression where
{
    import Import;
    import GHC.Exts(Constraint);

    data ConstraintWitness (constraint :: Constraint) where
    {
        MkConstraintWitness :: constraint => ConstraintWitness constraint;
    };

    listTypeToList :: (forall a. w a -> r) -> ListType w t -> [r];
    listTypeToList _wr NilListType = [];
    listTypeToList wr (ConsListType wa rest) = (wr wa):(listTypeToList wr rest);

    listTypeMap :: (forall a. w1 a -> w2 a) -> ListType w1 t -> ListType w2 t;
    listTypeMap _ww NilListType = NilListType;
    listTypeMap ww (ConsListType wa rest) = ConsListType (ww wa) (listTypeMap ww rest);

    listIdentity :: ListType Identity t -> t;
    listIdentity NilListType = ();
    listIdentity (ConsListType (Identity a) rest) = (a,listIdentity rest);

    listSequence ::  (Applicative f) => ListType f t -> f t;
    listSequence NilListType = pure ();
    listSequence (ConsListType fa rest) = liftA2 (,) fa (listSequence rest);

    class AppendList la lb where
    {
        type ListAppend la lb :: *;
        listAppendWitness :: ListType w la -> ListType w lb -> ListType w (ListAppend la lb);
        listJoin :: la -> lb -> ListAppend la lb;
        listSplit :: ListAppend la lb -> (la,lb);
    };

    instance AppendList () lb where
    {
        type ListAppend () lb = lb;
        listAppendWitness NilListType wlb = wlb;
        listJoin () lb = lb;
        listSplit lb = ((),lb);
    };

    instance (AppendList la lb) => AppendList (a,la) lb where
    {
        type ListAppend (a,la) lb = (a,ListAppend la lb);
        listAppendWitness (ConsListType wa wla) wlb = ConsListType wa (listAppendWitness wla wlb);
        listJoin (a,la) lb = (a,listJoin la lb);
        listSplit (a,lab) = case listSplit lab of
        {
            (la,lb) -> ((a,la),lb);
        };
    };

    witnessedListAppend :: ListType w la -> ListType w lb -> ConstraintWitness (AppendList la lb);
    witnessedListAppend NilListType _ = MkConstraintWitness;
    witnessedListAppend (ConsListType _ wla) wlb = case witnessedListAppend wla wlb of
    {
        MkConstraintWitness -> MkConstraintWitness;
    };
    
    
    newtype Opposite cc a b = MkOpposite (cc b a);
    
    class Thing cc where
    {
        thingUnit :: cc () ();
        thingPair :: cc a1 b1 -> cc a2 b2 -> cc (a1,a2) (b1,b2);
    };
    
    instance Thing (->) where
    {
        thingUnit = id;
        thingPair ab1 ab2 (a1,a2) = (ab1 a1,ab2 a2);
    };
    
    instance (Thing cc) => Thing (Opposite cc) where
    {
        thingUnit = MkOpposite thingUnit;
        thingPair (MkOpposite ab1) (MkOpposite ab2) = MkOpposite (thingPair ab1 ab2);
    };
    
    type MapWitness cc w1 w2 = forall r v1. w1 v1 -> (forall v2. w2 v2 -> (cc v1 v2) -> r) -> r;

    data MapList cc w2 l = forall lr. MkMapList
    {
        listMapWitness :: ListType w2 lr,
        listMap :: cc l lr
    };
    
    mapList :: (Thing cc) => MapWitness cc w1 w2 -> ListType w1 l -> MapList cc w2 l;
    mapList _ NilListType = MkMapList
    {
        listMapWitness = NilListType,
        listMap = thingUnit
    };
    mapList mapwit (ConsListType w rest) = case mapList mapwit rest of
    {
        MkMapList wit listMap' -> mapwit w (\w' vmap -> MkMapList
        {
            listMapWitness = ConsListType w' wit,
            listMap = thingPair vmap listMap'
        });
    };

    data RemoveFromList w a l = forall lr. MkRemoveFromList
    {
        listRemoveWitness :: ListType w lr,
        listInsert :: a -> lr -> l,
        listRemove :: l -> lr
    };

    removeAllMatching :: (SimpleWitness w) => w a -> ListType w l -> RemoveFromList w a l;
    removeAllMatching _ NilListType = MkRemoveFromList
    {
        listRemoveWitness = NilListType,
        listInsert = \_ -> id,
        listRemove = id
    };
    removeAllMatching wa (ConsListType wb rest) = case removeAllMatching wa rest of
    {
        MkRemoveFromList wit ins rm -> case matchWitness wa wb of
        {
            Just MkEqualType -> MkRemoveFromList
            {
                listRemoveWitness = wit,
                listInsert = \a l2 -> (a,ins a l2),
                listRemove = \(_,l1) -> rm l1
            };
            Nothing -> MkRemoveFromList
            {
                listRemoveWitness = ConsListType wb wit,
                listInsert = \a (b,l2) -> (b,ins a l2),
                listRemove = \(b,l1) -> (b,rm l1)
            };
        };
    };

    data RemoveManyFromList wit lx l = forall lr. MkRemoveManyFromList
    {
        listRemoveManyWitness :: ListType wit lr,
        listInsertMany :: lx -> lr -> l,
        listRemoveMany :: l -> lr
    };

    removeAllMatchingMany :: (SimpleWitness wit) => ListType wit lx -> ListType wit l -> RemoveManyFromList wit lx l;
    removeAllMatchingMany NilListType wl = MkRemoveManyFromList
    {
        listRemoveManyWitness = wl,
        listInsertMany = \_ lr -> lr,
        listRemoveMany = \l -> l
    };
    removeAllMatchingMany (ConsListType wa wlx) wl = case removeAllMatching wa wl of
    {
        MkRemoveFromList wl' ins rm -> case removeAllMatchingMany wlx wl' of
        {
            MkRemoveManyFromList wl'' insM remM -> MkRemoveManyFromList
            {
                listRemoveManyWitness = wl'',
                listInsertMany = \(a,lx) lr -> ins a (insM lx lr),
                listRemoveMany = remM . rm
            };
        };
    };

    newtype EitherWitness w1 w2 a = MkEitherWitness (Either (w1 a) (w2 a));

    data PartitionList wit1 wit2 l = forall l1 l2. MkPartitionList
    {
        listPartitionWitness1 :: ListType wit1 l1,
        listPartitionWitness2 :: ListType wit2 l2,
        listFromPartition :: l1 -> l2 -> l,
        listToPartition1 :: l -> l1,
        listToPartition2 :: l -> l2
    };

    partitionList :: ListType (EitherWitness w1 w2) l -> PartitionList w1 w2 l;
    partitionList NilListType = MkPartitionList
    {
        listPartitionWitness1 = NilListType,
        listPartitionWitness2 = NilListType,
        listFromPartition = \() () -> (),
        listToPartition1 = \() -> (),
        listToPartition2 = \() -> ()
    };
    partitionList (ConsListType (MkEitherWitness (Left w1a)) rest) = case partitionList rest of
    {
        MkPartitionList pw1 pw2 fp tp1 tp2 -> MkPartitionList
        {
            listPartitionWitness1 = ConsListType w1a pw1,
            listPartitionWitness2 = pw2,
            listFromPartition = \(a,l1) l2 -> (a,fp l1 l2),
            listToPartition1 = \(a,l) -> (a,tp1 l),
            listToPartition2 = \(_,l) -> tp2 l
        };
    };
    partitionList (ConsListType (MkEitherWitness (Right w2a)) rest) = case partitionList rest of
    {
        MkPartitionList pw1 pw2 fp tp1 tp2 -> MkPartitionList
        {
            listPartitionWitness1 = pw1,
            listPartitionWitness2 = ConsListType w2a pw2,
            listFromPartition = \l1 (a,l2) -> (a,fp l1 l2),
            listToPartition1 = \(_,l) -> tp1 l,
            listToPartition2 = \(a,l) -> (a,tp2 l)
        };
    };




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
            MkConstraintWitness -> MkExpression (listAppendWitness wits1 wits2) (liftA2 (\v1ab v2a v12 -> case listSplit v12 of
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
            MkConstraintWitness -> MkExpression (listAppendWitness wits1 wits2) (liftA2 (\(v1,ab) (v2,a) -> (listJoin v1 v2,ab a)) fcvab fcva);
        }
    };

    valueSymbolMap :: (Functor f) =>
     MapWitness (Opposite (->)) wit1 wit2 -> ValueExpression wit1 f r -> ValueExpression wit2 f r;
    valueSymbolMap mapwit (MkExpression wits fcvr) = case mapList mapwit wits of
    {
        MkMapList wits' (MkOpposite mapvals) -> MkExpression wits' (fmap (\valsr -> valsr . mapvals) fcvr);
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
        MkConstraintWitness -> MkExpression (listAppendWitness wits1 wits2) (Compose (\p -> do
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
