--------------------------------------------------------------------------------
-- BEGIN: PolynomialOIAlgebra.m2 -----------------------------------------------
--------------------------------------------------------------------------------

-- Define the new type PolynomialOIAlgebra
-- COMMENT: Should be of the form {baseField => Ring, varRows => ZZ, varSym => Symbol, algebras => MutableHashTable, maps => MutableHashTable}
PolynomialOIAlgebra = new Type of HashTable
PolynomialOIAlgebra.synonym = "polynomial OI-algebra"

toString PolynomialOIAlgebra := P -> "base field => "|toString P.baseField|", variable rows => "|toString P.varRows|", variable symbol => "|toString P.varSym

net PolynomialOIAlgebra := P -> "Base field: "|net P.baseField ||
    "Number of variable rows: "|net P.varRows ||
    "Variable symbol: "|net P.varSym

-- PURPOSE: Make a new PolynomialOIAlgebra
-- INPUT: '(K, c, x)', a field of coefficients 'K', a positive integer 'c' of rows and a variable symbol 'x'
-- OUTPUT: A PolynomialOIAlgebra made from K, c, x
makePolynomialOIAlgebra = method(TypicalValue => PolynomialOIAlgebra)
makePolynomialOIAlgebra(Ring, ZZ, Symbol) := (K, c, x) ->
    new PolynomialOIAlgebra from {
        baseField => K,
        varRows => c, 
        varSym => x, 
        algebras => new MutableHashTable, 
        maps => new MutableHashTable}

-- PURPOSE: Get the linearized index of a variable from its row-col position
-- INPUT: '(P, n, i, j)', a PolynomialOIAlgebra 'P', an integer 'n', a row 'i' and a column 'j'
-- OUTPUT: The index of x_(i,j) in the list of variables ordered so that in P_n we have x_(i,j) > x_(i',j') iff j > j' or j = j' and i > i'
linearFromRowCol = method(TypicalValue => ZZ)
linearFromRowCol(PolynomialOIAlgebra, ZZ, ZZ, ZZ) := (P, n, i, j) -> (
    if n == 0 then return null;
    P.varRows * (n - j + 1) - i
)

-- PURPOSE: Get the algebra from a PolynomialOIAlgebra in a specified width
-- INPUT: '(P, n)', a PolynomialOIAlgebra 'P' and a width 'n'
-- OUTPUT: P_n, the width n algebra of P
-- COMMENT: We use the "position down over term" monomial order and the standard ZZ-grading
getAlgebraInWidth = method(TypicalValue => PolynomialRing)
getAlgebraInWidth(PolynomialOIAlgebra, ZZ) := (P, n) -> (
    -- Return the algebra if it already exists
    if P.algebras#?n then return P.algebras#n;

    -- Generate the variables
    local ret;
    variables := new MutableList;
    for j from 1 to n do
        for i from 1 to P.varRows do variables#(linearFromRowCol(P, n, i, j)) = P.varSym_(i, j);
    
    -- Make the algebra
    ret = P.baseField[variables, Degrees => {#variables:1}, MonomialOrder => {Position => Down, Lex}];

    -- Store the algebra
    P.algebras#n = ret;

    ret
)

-- PURPOSE: Subscript version of getAlgebraInWidth
PolynomialOIAlgebra _ ZZ := (P, n) -> getAlgebraInWidth(P, n)

-- PURPOSE: Get the algebra map induced by an OI-map
-- INPUT: '(P, f)', a PolynomialOIAlgebra 'P' and an OIMap 'f'
-- OUTPUT: The map P(f)
getInducedAlgebraMap = method(TypicalValue => RingMap)
getInducedAlgebraMap(PolynomialOIAlgebra, OIMap) := (P, f) -> (
    -- Return the map if it already exists
    if P.maps#?(f.Width, f.assignment) then return P.maps#(f.Width, f.assignment);
    
    -- Generate the map
    m := #f.assignment;
    n := f.Width;
    src := getAlgebraInWidth(P, m);
    targ := getAlgebraInWidth(P, n);
    subs := new List;
    for j from 1 to m do
        for i from 1 to P.varRows do subs = append(subs, src_(linearFromRowCol(P, m, i, j)) => targ_(linearFromRowCol(P, n, i, f.assignment#(j - 1))));
    
    -- Make the map
    ret := map(targ, src, subs);

    -- Store the map
    P.maps#(f.Width, f.assignment) = ret;

    ret
)

-- PURPOSE: Get the induced algebra maps between two widths
-- INPUT: '(P, m, n)', a PolynomialOIAlgebra 'P', a width 'm' and a width 'n'
-- OUTPUT: A list of the elements in P(Hom(m, n))
getInducedAlgebraMaps = method(TypicalValue => List)
getInducedAlgebraMaps(PolynomialOIAlgebra, ZZ, ZZ) := (P, m, n) -> (
    if n < m then return {};
    
    -- Get the maps
    ret := new List;
    oiMaps := getOIMaps(m, n);
    for oiMap in oiMaps do ret = append(ret, getInducedAlgebraMap(P, oiMap));

    ret
)

--------------------------------------------------------------------------------
-- END: PolynomialOIAlgebra.m2 -------------------------------------------------
--------------------------------------------------------------------------------