module [
    empty,
    single,
    insert,
    len,
    isEmpty,
    remove,
    contains,
    get,
    toList,
    fromList,
    walk,
    walkUntil,
    map,
    joinMap,
    keepIf,
    dropIf,
    min,
    max,
    equal,
]

Comparison : [LessThan, Equal, GreaterThan]
Sort implements
    compare : a, a -> Comparison where a implements Sort

Entry k v := [Full k v, Key k] where k implements Sort
    implements [
        Sort {
            compare: entryCompare,
        },
    ]

toEntry : k, v -> Entry k v
toEntry = \k, v ->
    @Entry (Full k v)

entryKey : Entry k * -> k
entryKey = \@Entry entry ->
    when entry is
        Full k _ -> k
        Key k -> k

entryCompare : Entry k v, Entry k v -> Comparison
entryCompare = \l, r ->
    compare (entryKey l) (entryKey r)

TreeDict k v := { tree : RBT (Entry k v), size : U64 }
    implements [
        Eq {
            isEq: equal,
        },
    ]

# To get O(n) equality checking, I transform one of the maps to a list, then walkUntil the other map with an
# index as the state, comparing the key-value pairs to the pair in the list at the index. Since we stop early
# if something is not equal, we know the final index only equals the size if the maps are equal
equal : TreeDict k v, TreeDict k v -> Bool where v implements Bool.Eq
equal = \@TreeDict a, @TreeDict b ->
    if
        a.size == b.size
    then
        bList = toList (@TreeDict b)
        f = \i, entryA ->
            entryB = List.get bList i
            when (entryA, entryB) is
                (@Entry (Full keyA valueA), Ok (keyB, valueB)) ->
                    if
                        compare keyA keyB == Equal && valueA == valueB
                    then
                        Continue (i + 1)
                    else
                        Break i

                (_, Err _) -> crash "Did we not just check the length?"
                (_, _) -> crash "How did a Key entry get inserted?"
        endingIndex = rbtWalkUntil a.tree 0 f
        endingIndex == a.size
    else
        Bool.false

## Creates a new empty `TreeDict`.
## Note: The curly braces in the example are required.
## ```
## emptyDict = TreeDict.empty {}
## countEntries = TreeDict.len emptySet
##
## expect countEntries == 0
## ```
empty : {} -> TreeDict * *
empty = \{} -> @TreeDict { tree: E, size: 0 }

## Creates a new `TreeDict` with a single entry
single : k, v -> TreeDict k v
single = \key, value ->
    entry = toEntry key value
    @TreeDict { tree: rbtInsert E entry, size: 1 }

## Insert a value into the dictionary at a specified key.
## If the dictionary already had a value for the key, the returned dictionary contains the new value at the key.
insert : TreeDict k v, k, v -> TreeDict k v
insert = \@TreeDict dict, key, value ->
    entry = toEntry key value
    if
        rbtContains dict.tree entry
    then
        # Insert even if it already exists in order to update value
        @TreeDict { tree: rbtInsert dict.tree entry, size: dict.size }
    else
        @TreeDict { tree: rbtInsert dict.tree entry, size: (dict.size + 1) }

## Returns the number of values in the dictionary.
len : TreeDict * * -> U64
len = \@TreeDict dict -> dict.size

## Check if the dictionary is empty.
isEmpty : TreeDict * * -> Bool
isEmpty = \@TreeDict dict -> dict.size == 0

## Remove a value from the dictionary for a specified key.
remove : TreeDict k v, k -> TreeDict k v
remove = \@TreeDict dict, key ->
    entry = @Entry (Key key)
    if
        rbtContains dict.tree entry
    then
        @TreeDict { tree: rbtDelete dict.tree entry, size: (dict.size - 1) }
    else
        @TreeDict dict

## Get the value for a given key. If there is a value for the specified key it will return `[Ok value]`,
## otherwise return `[Err KeyNotFound]`.
## ```
## dictionary =
##     empty {}
##     |> insert (@TestNum 1) "Google"
##     |> insert (@TestNum 2) "Alexa"
##
## expect get dictionary (@TestNum 1) == Ok "Google"
## expect get dictionary (@TestNum 2000) == Err KeyNotFound
## ```
get : TreeDict k v, k -> Result v [KeyNotFound]
get = \@TreeDict dict, key ->
    entry = @Entry (Key key)
    when rbtGet dict.tree entry is
        Ok e ->
            when e is
                @Entry (Full _ value) -> Ok value
                _ -> crash "How did a Key entry get inserted?"

        Err NotFound -> Err KeyNotFound

## Check if the dictionary has a value for a specified key.
contains : TreeDict k v, k -> Bool
contains = \@TreeDict dict, key ->
    entry = @Entry (Key key)
    rbtContains dict.tree entry

fromList : List (k, v) -> TreeDict k v where a implements Sort
fromList = \xs ->
    f = \dict, (key, value) -> insert dict key value
    List.walk xs (empty {}) f

toList : TreeDict k v -> List (k, v)
toList = \@TreeDict dict ->
    f = \state, entry ->
        when entry is
            @Entry (Full key value) -> List.append state (key, value)
            _ -> crash "How did a Key entry get inserted?"
    rbtWalk dict.tree (List.withCapacity dict.size) f

walk : TreeDict k v, state, (state, k, v -> state) -> state
walk = \@TreeDict dict, state, f ->
    f2 = \state2, entry ->
        when entry is
            @Entry (Full key value) -> f state2 key value
            _ -> crash "How did a Key entry get inserted?"
    rbtWalk dict.tree state f2

walkUntil : TreeDict k v, state, (state, k, v -> [Continue state, Break state]) -> state
walkUntil = \@TreeDict dict, state, f ->
    f2 = \state2, entry ->
        when entry is
            @Entry (Full key value) -> f state2 key value
            _ -> crash "How did a Key entry get inserted?"
    rbtWalkUntil dict.tree state f2

map : TreeDict k a, (k, a -> b) -> TreeDict k b
map = \@TreeDict dict, f ->
    f2 = \entry ->
        when entry is
            @Entry (Full key value) -> @Entry (Full key (f key value))
            _ -> crash "How did a Key entry get inserted?"
    when rbtMap dict.tree f2 is
        Err InvalidatesTree -> crash "How did updating the value change the key compare?"
        Ok tree2 -> @TreeDict { tree: tree2, size: dict.size }

joinMap : TreeDict k a, (k, a -> TreeDict k b) -> TreeDict k b
joinMap = \dict, f ->
    f2 = \(key, value) ->
        f key value |> toList
    dict |> toList |> List.joinMap f2 |> fromList

keepIf : TreeDict k a, (k, a -> Bool) -> TreeDict k a
keepIf = \dict, predicate ->
    f = \state, key, value ->
        if
            predicate key value
        then
            insert state key value
        else
            state
    walk dict (empty {}) f

dropIf : TreeDict k a, (k, a -> Bool) -> TreeDict k a
dropIf = \dict, predicate ->
    f = \state, key, value ->
        if
            predicate key value
        then
            state
        else
            insert state key value
    walk dict (empty {}) f

min : TreeDict k v -> Result (k, v) [EmptyTree]
min = \@TreeDict dict ->
    when rbtMin dict.tree is
        Err EmptyTree -> Err EmptyTree
        Ok (@Entry (Full key value)) -> Ok (key, value)
        Ok (@Entry _) -> crash "How did a Key entry get inserted?"

max : TreeDict k v -> Result (k, v) [EmptyTree]
max = \@TreeDict dict ->
    when rbtMax dict.tree is
        Err EmptyTree -> Err EmptyTree
        Ok (@Entry (Full key value)) -> Ok (key, value)
        Ok (@Entry _) -> crash "How did a Key entry get inserted?"

# ---- test code ----

# Test single and isEmpty
expect !(single (@TestNum 2) 3 |> isEmpty)
expect single (@TestNum 2) 3 |> remove (@TestNum 2) |> isEmpty

# Test remove and len
expect (single (@TestNum 2) 3 |> len) == 1
expect (single (@TestNum 2) 3 |> remove (@TestNum 3) |> len) == 1
expect (single (@TestNum 2) 3 |> remove (@TestNum 2) |> len) == 0

# Test empty and insert
expect !(empty {} |> insert (@TestNum 2) 3 |> isEmpty)
expect empty {} |> insert (@TestNum 2) 3 |> remove (@TestNum 2) |> isEmpty

# Test get
dictionary =
    empty {}
    |> insert (@TestNum 2) "Alexa"
    |> insert (@TestNum 1) "Google"
expect get dictionary (@TestNum 1) == Ok "Google"
expect get dictionary (@TestNum 2000) == Err KeyNotFound

# Test contains
expect contains dictionary (@TestNum 2)
expect !(contains dictionary (@TestNum 3))

# Test walk
expect
    dict = single (@TestNum 1) 3 |> insert (@TestNum 2) 5
    f = \state, _, value -> state + value
    walk dict 0 f == 8

# Test fromList, equal, walkUntil (the implementation of equal uses walkUntil)
expect fromList [(@TestNum 1, "Google"), (@TestNum 2, "Alexa")] == dictionary
expect fromList [(@TestNum 1, "Google"), (@TestNum 2, "Cortana")] != dictionary

# Test toList
expect toList dictionary |> fromList == dictionary
expect toList dictionary == [(@TestNum 1, "Google"), (@TestNum 2, "Alexa")]

# Test map
expect
    f = \_, s -> Str.concat s ", sup"
    expected = single (@TestNum 1) "Google, sup" |> insert (@TestNum 2) "Alexa, sup"
    expected == map dictionary f

# Test joinMap
expect
    f = \n, s ->
        single n s |> insert (succ n) (Str.concat s " +1")
    expected = single (@TestNum 1) "Google" |> insert (@TestNum 2) "Alexa" |> insert (@TestNum 3) "Alexa +1"
    expected == joinMap dictionary f

# Test keepIf
expect
    p = \@TestNum n, _ -> n % 2 == 1
    expected = single (@TestNum 1) "Google"
    expected == keepIf dictionary p

# Test dropIf
expect
    p = \@TestNum n, _ -> n % 2 == 1
    expected = single (@TestNum 2) "Alexa"
    expected == dropIf dictionary p

# Test min
expect min dictionary == Ok (@TestNum 1, "Google")

# Test max
expect max dictionary == Ok (@TestNum 2, "Alexa")

TestNum := I64
    implements [
        Sort {
            compare: compareTestNum,
        },
        Eq,
    ]

compareTestNum : TestNum, TestNum -> Comparison
compareTestNum = \@TestNum l, @TestNum r ->
    if l < r then
        LessThan
    else if l == r then
        Equal
    else
        GreaterThan

succ : TestNum -> TestNum
succ = \@TestNum n ->
    @TestNum (n + 1)

# ---- Reb Black Tree ----

Color : [R, B]
RBT a : [
    E,
    T Color (RBT a) a (RBT a),
] where a implements Sort

rbtMap : RBT a, (a -> b) -> Result (RBT b) [InvalidatesTree] where a implements Sort, b implements Sort
rbtMap = \t, f ->
    when t is
        E -> Ok E
        T c l v r ->
            when rbtMap l f is
                Err InvalidatesTree -> Err InvalidatesTree
                Ok l2 ->
                    when rbtMap r f is
                        Err InvalidatesTree -> Err InvalidatesTree
                        Ok r2 ->
                            v2 = f v
                            t2 = T c l2 v2 r2
                            if
                                rbtMapCompare l2 t2 && rbtMapCompare t2 r2
                            then
                                Ok t2
                            else
                                Err InvalidatesTree

rbtMapCompare : RBT a, RBT a -> Bool where a implements Sort
rbtMapCompare = \l, r ->
    when (l, r) is
        (T _ _ lv _, T _ _ rv _) -> compare lv rv == LessThan
        (_, _) -> Bool.true

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
