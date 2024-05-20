module [
    empty,
    single,
    insert,
    len,
    isEmpty,
    remove,
    contains,
    toList,
    fromList,
    union,
    intersection,
    difference,
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

TreeSet k := { tree : RBT k, size : U64 }
    implements [
        Eq {
            isEq: equal,
        },
    ]

## Creates a new empty `TreeSet`.
## Note: The curly braces in the example are required.
## ```
## emptySet = TreeSet.empty {}
## countValues = TreeSet.len emptySet
##
## expect countValues == 0
## ```
empty : {} -> TreeSet *
empty = \{} -> @TreeSet { tree: E, size: 0 }

## Creates a new `TreeSet` with a single value.
single : k -> TreeSet k where k implements Sort
single = \elem ->
    @TreeSet { tree: rbtInsert E elem, size: 1 }

## Insert a value into a `TreeSet`.
## Note, if the element is in the set, the returned set contains the element passed in rather than the original.
## This is only important when Equal is an equivalence relation rather than structural equality.
insert : TreeSet k, k -> TreeSet k where k implements Sort
insert = \@TreeSet set, elem ->
    if
        rbtContains set.tree elem
    then
        @TreeSet { tree: rbtInsert set.tree elem, size: set.size }
    else
        @TreeSet { tree: rbtInsert set.tree elem, size: (set.size + 1) }

## Counts the number of values in a given `TreeSet`.
len : TreeSet * -> U64
len = \@TreeSet set -> set.size

## Check if the set is empty.
isEmpty : TreeSet * -> Bool
isEmpty = \@TreeSet set -> set.size == 0

## Removes the value from the given `TreeSet`.
remove : TreeSet k, k -> TreeSet k
remove = \@TreeSet set, elem ->
    if
        rbtContains set.tree elem
    then
        @TreeSet { tree: rbtDelete set.tree elem, size: (set.size - 1) }
    else
        @TreeSet set

## Test if a value is in the `TreeSet`.
contains : TreeSet k, k -> Bool
contains = \@TreeSet set, elem ->
    rbtContains set.tree elem

## Retrieve the values in a `TreeSet` as a `List`.
toList : TreeSet k -> List k
toList = \@TreeSet set ->
    rbtAppendToList (List.withCapacity set.size) set.tree

## Create a `TreeSet` from a List of values.
fromList : List k -> TreeSet k where k implements Sort
fromList = \xs ->
    List.walk xs (empty {}) insert

## Create a `TreeSet` containing all the values from both the input sets.
union : TreeSet k, TreeSet k -> TreeSet k
union = \@TreeSet setA, @TreeSet setB ->
    smallSet = if setA.size < setB.size then setA else setB
    bigSet = if setA.size < setB.size then setB else setA
    rbtWalk smallSet.tree (@TreeSet bigSet) insert

## Create a `TreeSet` only containing values which are in both input sets.
intersection : TreeSet k, TreeSet k -> TreeSet k
intersection = \@TreeSet setA, @TreeSet setB ->
    smallSet = if setA.size < setB.size then setA else setB
    bigSet = if setA.size < setB.size then setB else setA
    f = \@TreeSet set, elem ->
        if
            contains (@TreeSet bigSet) elem
        then
            insert (@TreeSet set) elem
        else
            @TreeSet set
    rbtWalk smallSet.tree (empty {}) f

## Create a `TreeSet` containing values from the first set which are NOT in the second set.
difference : TreeSet k, TreeSet k -> TreeSet k
difference = \@TreeSet setA, @TreeSet setB ->
    f = \@TreeSet set, elem ->
        if
            contains (@TreeSet setB) elem
        then
            @TreeSet set
        else
            insert (@TreeSet set) elem
    rbtWalk setA.tree (empty {}) f

## Iterate through the values of a given `TreeSet` and build a value.
##
## Names for this in other languages include `reduce` and `fold`.
walk : TreeSet k, state, (state, k -> state) -> state
walk = \@TreeSet set, state, f ->
    rbtWalk set.tree state f

## Same as `walk`, except you can stop walking early.
## Can have improve performance if breaking early is common.
walkUntil : TreeSet k, state, (state, k -> [Continue state, Break state]) -> state
walkUntil = \@TreeSet set, state, f ->
    rbtWalkUntil set.tree state f

## Create a `TreeSet` containing the values of the input `TreeSet`
## after transforming them with the input function.
##
## N.B. The output `TreeSet` may have fewer elements than the input `TreeSet`
## If the function maps multiple input elements to the same output element.
map : TreeSet a, (a -> b) -> TreeSet b
map = \set, f ->
    set |> toList |> List.map f |> fromList

## Like `map`, except the transformation function wraps the return value in a set.
## At the end, all the sets get joined together (using `union`) into one set.
##
## Names for this in other languages include `flatMap`, `concatMap`, and `bind`.
joinMap : TreeSet a, (a -> TreeSet b) -> TreeSet b
joinMap = \set, f ->
    set |> toList |> List.map f |> List.walk (empty {}) union

## Run the given function on each element in the Set,
## and return a Set with just the elements for which the function returned Bool.true.
keepIf : TreeSet k, (k -> Bool) -> TreeSet k
keepIf = \set, p ->
    f = \state, elem ->
        if
            p elem
        then
            insert state elem
        else
            state
    walk set (empty {}) f

## Run the given function on each element in the Set,
## and return a Set with just the elements for which the function returned Bool.false.
dropIf : TreeSet k, (k -> Bool) -> TreeSet k
dropIf = \set, p ->
    f = \state, elem ->
        if
            p elem
        then
            state
        else
            insert state elem
    walk set (empty {}) f

## Gets the smallest element in the `TreeSet`
min : TreeSet k -> Result k [EmptyTree]
min = \@TreeSet set ->
    rbtMin set.tree

## Gets the largest element in the `TreeSet`
max : TreeSet k -> Result k [EmptyTree]
max = \@TreeSet set ->
    rbtMax set.tree

equal : TreeSet k, TreeSet k -> Bool
equal = \@TreeSet setA, @TreeSet setB ->
    f = \_, elem ->
        if
            contains (@TreeSet setB) elem
        then
            Continue Bool.true
        else
            Break Bool.false
    setA.size
    == setB.size
    && rbtWalkUntil setA.tree Bool.true f

# ---- RBT ----
#
# N.B. All the "rbt"s here stand for Red Black Tree, not to be confused with Roc Build Tool

Color : [R, B]
RBT a : [
    E,
    T Color (RBT a) a (RBT a),
] where a implements Sort

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

# ---- Test Code ----

expect (single (@TestNum 2) |> len) == 1
expect (single (@TestNum 2) |> insert (@TestNum 2) |> len) == 1
expect (single (@TestNum 2) |> insert (@TestNum 3) |> len) == 2

expect !(single (@TestNum 2) |> isEmpty)

expect (single (@TestNum 2) |> remove (@TestNum 2) |> len) == 0
expect single (@TestNum 2) |> remove (@TestNum 2) |> isEmpty
expect (single (@TestNum 2) |> insert (@TestNum 3) |> remove (@TestNum 2) |> len) == 1
expect !(single (@TestNum 2) |> insert (@TestNum 3) |> remove (@TestNum 2) |> contains (@TestNum 2))
expect single (@TestNum 2) |> insert (@TestNum 3) |> remove (@TestNum 2) |> contains (@TestNum 3)

# fromList and toList test
expect
    xs = [@TestNum 3, @TestNum 2, @TestNum 4]
    xs2 = fromList xs |> toList
    List.len xs2
    == 3
    && List.contains xs2 (@TestNum 2)
    && List.contains xs2 (@TestNum 3)
    && List.contains xs2 (@TestNum 4)

# fromListTest and contains test
expect
    set = fromList [@TestNum 3, @TestNum 2, @TestNum 3]
    len set == 2 && contains set (@TestNum 2) && contains set (@TestNum 3)

# union test
expect
    a = fromList [@TestNum 2, @TestNum 3]
    b = fromList [@TestNum 4, @TestNum 3, @TestNum 5]
    ab = union a b
    expected = fromList [@TestNum 2, @TestNum 4, @TestNum 3, @TestNum 5]
    ab == expected

# intersection test
expect
    a = fromList [@TestNum 2, @TestNum 3]
    b = fromList [@TestNum 4, @TestNum 3, @TestNum 5]
    ab = intersection a b
    expected = single (@TestNum 3)
    ab == expected

# difference test
expect
    a = fromList [@TestNum 2, @TestNum 3]
    b = fromList [@TestNum 4, @TestNum 3, @TestNum 5]
    ab = difference a b
    expected = single (@TestNum 2)
    ab == expected

# map test
expect
    set = fromList [@TestNum 4, @TestNum 3, @TestNum 5]
    expected = fromList [@TestNum 2, @TestNum 1]
    f = \@TestNum a ->
        @TestNum (a // 2)
    actual = map set f
    actual == expected

# joinMap test
expect
    set = fromList [@TestNum 1, @TestNum 3, @TestNum 0]
    expected = fromList [@TestNum 0, @TestNum 2, @TestNum -2, @TestNum 6, @TestNum -6]
    f = \@TestNum a ->
        single (@TestNum (a * 2)) |> insert (@TestNum (-(a * 2)))
    actual = joinMap set f
    actual == expected

# walk test
expect
    set = fromList [@TestNum 4, @TestNum 3, @TestNum 5]
    f = \s, @TestNum n -> s + n
    m = walk set 0 f
    expected = 12
    m == expected

# keepIf test
expect
    set = fromList [@TestNum 4, @TestNum 3, @TestNum 5]
    p = \@TestNum n -> n % 2 == 1
    expected = fromList [@TestNum 3, @TestNum 5]
    actual = keepIf set p
    actual == expected

# dropIf test
expect
    set = fromList [@TestNum 4, @TestNum 3, @TestNum 5]
    p = \@TestNum n -> n % 2 == 1
    expected = fromList [@TestNum 4]
    actual = dropIf set p
    actual == expected

# max test
expect
    set = fromList [@TestNum 4, @TestNum 3, @TestNum 5]
    expected = Ok (@TestNum 5)
    actual = max set
    actual == expected

# min test
expect
    set = fromList [@TestNum 4, @TestNum 3, @TestNum 5]
    expected = Ok (@TestNum 3)
    actual = min set
    actual == expected

# not equal test
expect
    a = fromList [@TestNum 4, @TestNum 3, @TestNum 6]
    b = fromList [@TestNum 4, @TestNum 3, @TestNum 5]
    !(a == b)

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

