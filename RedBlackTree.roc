module []

Comparison : [LessThan, Equal, GreaterThan]
Sort implements
    compare : a, a -> Comparison where a implements Sort

Color : [R, B]
RBT a : [
    E,
    T Color (RBT a) a (RBT a),
] where a implements Sort

rbtFromList : List a -> RBT a where a implements Sort
rbtFromList = \xs ->
    List.walk xs E rbtInsert

rbtToList : RBT a -> List a where a implements Sort
rbtToList = \t ->
    rbtAppendToList (List.withCapacity 8) t

rbtWalk : RBT a, state, (state, a -> state) -> state
rbtWalk = \t, state, f ->
    when t is
        E -> state
        T _ l v r ->
            lState = rbtWalk l state f
            vState = f lState v
            rbtWalk r vState f

rbtWalkUntil : RBT a, state, (state, a -> [Continue state, Break state]) -> state
rbtWalkUntil = \t, state, f ->
    result = rbtWalkUntilHelper t state f
    when result is
        Continue c -> c
        Break b -> b

rbtWalkUntilHelper : RBT a, state, (state, a -> [Continue state, Break state]) -> [Continue state, Break state]
rbtWalkUntilHelper = \t, state, f ->
    when t is
        E -> Continue state
        T _ l v r ->
            lResult = rbtWalkUntilHelper l state f
            when lResult is
                Break _ -> lResult
                Continue lState ->
                    vResult = f lState v
                    when vResult is
                        Break _ -> vResult
                        Continue vState ->
                            rbtWalkUntilHelper r vState f

rbtAppendToList : List a, RBT a -> List a
rbtAppendToList = \xs, t ->
    when t is
        E -> xs
        T _ l v r ->
            rbtAppendToList xs l |> List.append v |> rbtAppendToList r

rbtContains : RBT a, a -> Bool where a implements Sort
rbtContains = \t, x ->
    when t is
        E -> Bool.false
        T _ l y r ->
            when compare x y is
                LessThan -> rbtContains l x
                Equal -> Bool.true
                GreaterThan -> rbtContains r x

rbtGet : RBT a, a -> Result a [NotFound] where a implements Sort
rbtGet = \t, x ->
    when t is
        E -> Err NotFound
        T _ l y r ->
            when compare x y is
                LessThan -> rbtGet l x
                Equal -> Ok y
                GreaterThan -> rbtGet r x

rbtMin : RBT a -> Result a [EmptyTree] where a implements Sort
rbtMin = \t ->
    when t is
        T _ E v _ -> Ok v
        T _ l _ _ -> rbtMin l
        E -> Err EmptyTree

rbtMax : RBT a -> Result a [EmptyTree] where a implements Sort
rbtMax = \t ->
    when t is
        T _ _ v E -> Ok v
        T _ _ _ r -> rbtMax r
        E -> Err EmptyTree

## Uses e to look up value v and applies function "f" to it. If f of v compares Equal to v, v is replaced by f of v.
## This can be useful if Equal is an equivalence relation rather than structural equality.
## The use case which motivated this function is that of a SortedMap backed by RedBlackTree. This method allows the
## map to have an "adjust" method for updating the value of a key value pair
##      adjust : OrderedMap k v, k, (v -> f) -> OrderedMap
rbtAdjust : RBT a, a, (a -> a) -> RBT a where a implements Sort
rbtAdjust = \t, e, f ->
    when t is
        E -> E
        T c l v r ->
            when compare e v is
                LessThan -> rbtAdjust l e f
                GreaterThan -> rbtAdjust r e f
                Equal ->
                    v2 = f v
                    if
                        compare v v2 == Equal
                    then
                        T c l v2 r
                    else
                        t

rbtInsert : RBT a, a -> RBT a where a implements Sort
rbtInsert = \rbt, e ->
    insertHelper rbt e |> blacken

insertHelper : RBT a, a -> RBT a where a implements Sort
insertHelper = \t, e ->
    when t is
        E -> T R E e E
        T c a y b ->
            when compare e y is
                LessThan -> leftInsertBalance c (insertHelper a e) y b
                Equal -> T c a e b
                GreaterThan -> rightInsertBalance c a y (insertHelper b e)

rightInsertBalance : Color, RBT a, a, RBT a -> RBT a
rightInsertBalance = \color, l, v, r ->
    when (color, l, v, r) is
        (B, a, x, T R b y (T R c z d)) -> T R (T B a x b) y (T B c z d)
        (B, a, x, T R (T R b y c) z d) -> T R (T B a x b) y (T B c z d)
        (_, a, x, b) -> T color a x b

leftInsertBalance : Color, RBT a, a, RBT a -> RBT a
leftInsertBalance = \color, l, v, r ->
    when (color, l, v, r) is
        (B, T R a x (T R b y c), z, d) -> T R (T B a x b) y (T B c z d)
        (B, T R (T R a x b) y c, z, d) -> T R (T B a x b) y (T B c z d)
        (_, a, x, b) -> T color a x b

blacken : RBT a -> RBT a
blacken = \t ->
    when t is
        E -> E
        T _ l v r -> T B l v r

rbtDelete : RBT a, a -> RBT a where a implements Sort
rbtDelete = \t, v ->
    (tp, _) = deleteHelper t v
    blacken tp

deleteHelper : RBT a, a -> (RBT a, Bool) where a implements Sort
deleteHelper = \t, v ->
    when t is
        E -> (E, Bool.false)
        T c E w E ->
            when compare v w is
                Equal ->
                    if
                        c == B
                    then
                        (E, Bool.true)
                    else
                        (E, Bool.false)

                _ -> (t, Bool.false)

        T c E w r ->
            when compare v w is
                LessThan -> (t, Bool.false)
                Equal ->
                    if
                        c == B
                    then
                        (r, Bool.true)
                    else
                        (r, Bool.false)

                GreaterThan ->
                    (rp, needsBal) = deleteHelper r v
                    rightDeleteBalance (T c E w rp) needsBal

        T c l w E ->
            when compare v w is
                LessThan -> (t, Bool.false)
                Equal ->
                    if
                        c == B
                    then
                        (l, Bool.true)
                    else
                        (l, Bool.false)

                GreaterThan ->
                    (lp, needsBal) = deleteHelper l v
                    leftDeleteBalance (T c lp w E) needsBal

        T c l w r ->
            when compare v w is
                LessThan ->
                    (lp, needsBal) = deleteHelper l v
                    leftDeleteBalance (T c lp w r) needsBal

                Equal ->
                    wpResult = rbtMin r
                    when wpResult is
                        Ok wp ->
                            (rp, needsBal) = deleteHelper r wp
                            rightDeleteBalance (T c l wp rp) needsBal

                        Err EmptyTree -> crash "how could a not empty tree be empty?"

                GreaterThan ->
                    (rp, needsBal) = deleteHelper r v
                    rightDeleteBalance (T c l w rp) needsBal

leftDeleteBalance : RBT a, Bool -> (RBT a, Bool)
leftDeleteBalance = \t, needsBal ->
    if needsBal then
        when t is
            T B (T R xl x xr) p r -> (T B (T B xl x xr) p r, Bool.false)
            T B xt p (T R (T B lt g (T R rl rv rr)) s sr) -> (T B (T R (T B xt p lt) g (T B rl rv rr)) s sr, Bool.false)
            T B xt p (T R (T B (T R ll lv lr) g rt) s sr) -> (T B (T R (T B xt p ll) lv (T B lr g rt)) s sr, Bool.false)
            T B xt p (T R (T B lt g rt) s sr) -> (T B (T B xt p (T R lt g rt)) s sr, Bool.false)
            T cp xt p (T B gl s (T R grr gr grl)) -> (T cp (T B xt p gl) s (T B grr gr grl), Bool.false)
            T cp xt p (T B (T R gll gl glr) s gr) -> (T cp (T B xt p gll) gl (T B glr s gr), Bool.false)
            T cp tx p (T B gl g gr) -> (T cp tx p (T R gl g gr), Bool.true)
            _ -> crash "Red Black Tree violation. This should not be possible"
    else
        (t, needsBal)

rightDeleteBalance : RBT a, Bool -> (RBT a, Bool)
rightDeleteBalance = \t, needsBal ->
    if needsBal then
        when t is
            T B r p (T R xl x xr) -> (T B r p (T B xl x xr), Bool.false)
            T B (T R sl s (T B (T R ll lv lr) g rt)) p xt -> (T B sl s (T R (T B ll lv lr) g (T B rt p xt)), Bool.false)
            T B (T R sr s (T B rr g (T R lt rv rl))) p xt -> (T B sr s (T R (T B rr g lt) rv (T B rl p xt)), Bool.false)
            T B (T R sl s (T B lt g rt)) p xt -> (T B sl s (T B (T R lt g rt) p xt), Bool.false)
            T cp (T B (T R gll gl glr) s gr) p xt -> (T cp (T B gll gl glr) s (T B gr p xt), Bool.false)
            T cp (T B gl s (T R grl gr glr)) p xt -> (T cp (T B gl s grl) gr (T B glr p xt), Bool.false)
            T cp (T B gl g gr) p tx -> (T cp (T R gl g gr) p tx, Bool.true)
            _ -> crash "Red Black Tree violation. This should never happen"
    else
        (t, needsBal)

# ----- Test Code -----

expect rbtContains (fromIs [1, 2, 3]) (iToTn 3)
expect !(fromIs [1, 2, 3] |> rbtDelete (iToTn 2) |> rbtContains (iToTn 2))
expect (fromIs [2, 1, 3] |> rbtMin) == Ok (iToTn 1)
expect (fromIs [2, 1, 3] |> rbtMax) == Ok (iToTn 3)
expect (fromIs [123, 0, -321] |> rbtToList |> tnsToIs) == [-321, 0, 123]
expect (compare (entry (iToTn 5) "a") (entry (iToTn 5) "b")) == Equal
expect E |> rbtInsert (entry (iToTn 5) "a") |> rbtAdjust (entry (iToTn 5) "b") testUpdate |> rbtGet (entry (iToTn 5) "b") |> testValue "d"

Entry k v := { key : k, value : v } where k implements Sort
    implements [
        Sort {
            compare: entryCompare,
        },
    ]

entryCompare : Entry k v, Entry k v -> Comparison
entryCompare = \@Entry l, @Entry r ->
    compare l.key r.key

testUpdate : Entry k Str -> Entry k Str
testUpdate = \@Entry e ->
    @Entry { key: e.key, value: "d" }

testValue : Result (Entry k Str) [NotFound], Str -> Bool
testValue = \re, v ->
    when re is
        Err NotFound -> Bool.false
        Ok (@Entry e) -> e.value == v

TestNum := I64
    implements [
        Sort {
            compare: compareTestNum,
        },
        Eq,
    ]

entry = \k, v ->
    @Entry { key: k, value: v }

iToTn = \i ->
    @TestNum i

tnToI = \@TestNum i ->
    i

isToTns = \xs ->
    List.map xs iToTn

tnsToIs = \xs ->
    List.map xs tnToI

fromIs = \xs ->
    isToTns xs |> rbtFromList

compareTestNum : TestNum, TestNum -> Comparison
compareTestNum = \@TestNum l, @TestNum r ->
    if l < r then
        LessThan
    else if l == r then
        Equal
    else
        GreaterThan
