load "OI.m2"

--------------------------------------------------------------------------------
-- BEGIN: PolynomialOIAlgebra.m2 -----------------------------------------------
--------------------------------------------------------------------------------

-- Define the new type PolynomialOIAlgebra
PolynomialOIAlgebra = new Type of HashTable

-- Install toString method for PolynomialOIAlgebra
toString PolynomialOIAlgebra := P -> "base field = "|toString P.baseField |", variable rows = "|toString P.varRows|", variable symbol = "|toString P.varSym

-- Install net method for PolynomialOIAlgebra
net PolynomialOIAlgebra := P -> "Base field: "|net P.baseField ||
    "Number of variable rows: "|net P.varRows ||
    "Variable symbol: "|net P.varSym

-- PURPOSE: Check if a given PolynomialOIAlgebra object is valid
-- INPUT: A PolynomialOIAlgebra 'P'
-- OUTPUT: Nothing if P is a valid PolynomialOIAlgebra object, otherwise error
assertValid PolynomialOIAlgebra := P -> (
    if not sort keys P == sort {baseField, varRows, varSym, algebras, maps} then error("Invalid PolynomialOIAlgebra HashTable keys: "|toString keys P);
    if not instance(P.baseField, Ring) or not isField P.baseField then error("Expected a field, instead got "|toString P.baseField);
    if not instance(P.varRows, ZZ) or P.varRows < 1 then error("Expected a positive integer row count, instead got "|toString P.varRows);
    if not instance(P.varSym, Symbol) then error("Expected variable symbol, instead got "|toString P.varSym);
    if not instance(P.algebras, MutableHashTable) then error("Expected type MutableHashTable for algebras, instead got "|toString class P.algebras);
    if not instance(P.maps, MutableHashTable) then error("Expected type MutableHashTable for maps, instead got "|toString class P.maps)
)

-- PURPOSE: Make a new PolynomialOIAlgebra
-- INPUT: '(K, c, x)', a field of coefficients 'K', a positive integer 'c' of rows and a variable symbol 'x'
-- OUTPUT: A PolynomialOIAlgebra made from K, c, x
polynomialOIAlgebra = method(TypicalValue => PolynomialOIAlgebra)
polynomialOIAlgebra(Ring, ZZ, Symbol) := (K, c, x) -> (
    P := new PolynomialOIAlgebra from {baseField => K, varRows => c, varSym => x, algebras => new MutableHashTable, maps => new MutableHashTable};
    assertValid P;
    P
)

-- PURPOSE: Get the linearized index of a variable from its row-col position
-- INPUT: '(P, n, i, j)', a PolynomialOIAlgebra 'P', a width 'n', a row 'i' and a column 'j'
-- OUTPUT: The index of x_(i,j) in the list of variables ordered so that in P_n we have x_(i,j) > x_(i',j') iff j > j' or j = j' and i > i'
linearFromRowCol = method(TypicalValue => ZZ)
linearFromRowCol(PolynomialOIAlgebra, ZZ, ZZ, ZZ) := (P, n, i, j) -> (
    scan({P, n}, assertValid);
    if n == 0 then return null;
    if i < 1 or i > P.varRows then error("Expected row between 1 and "|toString P.varRows|", instead got "|toString i);
    if j < 1 or j > n then error("Expected column between 1 and "|toString n|", instead got "|toString j);

    P.varRows * (n - j + 1) - i
)

-- PURPOSE: Get the algebra from a PolynomialOIAlgebra in a specified width
-- INPUT: '(P, n)', a PolynomialOIAlgebra 'P' and a width 'n'
-- OUTPUT: P_n, the width n algebra of P
-- COMMENT: We use the "position down over term" monomial order and the standard ZZ-grading
-- COMMENT: "Store => false" will not store the algebra in memory (useful for large computations)
getAlgebraInWidth = method(TypicalValue => PolynomialRing, Options => {Store => true})
getAlgebraInWidth(PolynomialOIAlgebra, ZZ) := opts -> (P, n) -> (
    scan({P, n}, assertValid);
    if not instance(opts.Store, Boolean) then error("Expected boolean value for Store option, instead got "|toString opts.Store);

    -- Return the algebra if it already exists
    if (P.algebras)#?n then return (P.algebras)#n;

    -- Generate the variables
    local ret;
    variables := new MutableList;
    for j from 1 to n do
        for i from 1 to P.varRows do variables#(linearFromRowCol(P, n, i, j)) = (P.varSym)_(i, j);
    
    -- Make a new algebra
    ret = P.baseField[variables, Degrees => {#variables:1}, MonomialOrder => {Position => Down, Lex}];

    -- Store the algebra
    if opts.Store then (P.algebras)#n = ret;

    ret
)

-- PURPOSE: Subscript version of getAlgebraInWidth
PolynomialOIAlgebra _ ZZ := (P, n) -> getAlgebraInWidth(P, n)

-- PURPOSE: Get the maps between two algebras in a PolynomialOIAlgebra
-- INPUT: '(P, m, n)', a PolynomialOIAlgebra 'P', a width 'm' and a width 'n' with m ≤ n
-- OUTPUT: A list of the "OI-induced" algebra maps between P_m and P_n, i.e. P(Hom(m, n))
-- COMMENT: "Store => false" will not store the maps in memory (useful for large computations)
getAlgebraMapsBetweenWidths = method(TypicalValue => List, Options => {Store => true})
getAlgebraMapsBetweenWidths(PolynomialOIAlgebra, ZZ, ZZ) := opts -> (P, m, n) -> (
    scan({P, m, n}, assertValid);
    if n < m then error("Expected m ≤ n, instead got m = "|toString m|" and n = "|toString n);
    if not instance(opts.Store, Boolean) then error("Expected boolean value for Store option, instead got "|toString opts.Store);

    -- Return the maps if they already exist
    if (P.maps)#?(m, n) then return (P.maps)#(m, n);

    targ := getAlgebraInWidth(P, n, Store => opts.Store);
    src := getAlgebraInWidth(P, m, Store => opts.Store);

    local ret;
    algMaps := new List;
    oiMaps := getOIMaps(m, n);

    -- Generate algebra maps
    for oiMap in oiMaps do (
        subs := new List;

        for j from 1 to m do
            for i from 1 to P.varRows do subs = append(subs, src_(linearFromRowCol(P, m, i, j)) => targ_(linearFromRowCol(P, n, i, (oiMap#1)#(j - 1))));

        algMaps = append(algMaps, map(targ, src, subs))
    );
    ret = algMaps;

    -- Store the maps
    if opts.Store then (P.maps)#(m, n) = ret;

    ret
)

--------------------------------------------------------------------------------
-- END: PolynomialOIAlgebra.m2 -------------------------------------------------
--------------------------------------------------------------------------------