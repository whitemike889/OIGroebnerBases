--------------------------------------------------------------------------------
-- BEGIN: PolynomialOIAlgebra.m2 -----------------------------------------------
--------------------------------------------------------------------------------

-- Define the new type PolynomialOIAlgebra
-- COMMENT: Should be of the form {baseField => Ring, varRows => ZZ, varSym => Symbol, algebras => MutableHashTable, maps => MutableHashTable}
PolynomialOIAlgebra = new Type of HashTable
PolynomialOIAlgebra.synonym = "polynomial OI-algebra"

-- Install toString method for PolynomialOIAlgebra
toString PolynomialOIAlgebra := P -> "base field = "|toString P.baseField |", variable rows = "|toString P.varRows|", variable symbol = "|toString P.varSym

-- Install net method for PolynomialOIAlgebra
net PolynomialOIAlgebra := P -> "Base field: "|net P.baseField ||
    "Number of variable rows: "|net P.varRows ||
    "Variable symbol: "|net P.varSym

-- Verification method for PolynomialOIAlgebra
verifyData PolynomialOIAlgebra := P -> (
    if not sort keys P === sort {baseField, varRows, varSym, algebras, maps} then error("Expected keys {baseField, varRows, varSym, algebras, maps}, instead got "|toString keys P);
    if not instance(P.baseField, Ring) or not isField P.baseField then error("Expected a field for baseField, instead got "|toString P.baseField);
    if not instance(P.varRows, ZZ) or P.varRows < 1 then error("Expected a positive integer row count for varRows, instead got "|toString P.varRows);
    if not instance(P.varSym, Symbol) then error("Expected type Symbol for varSym, instead got type "|toString class P.varSym);
    if not instance(P.algebras, MutableHashTable) then error("Expected type MutableHashTable for algebras, instead got type "|toString class P.algebras);
    if not instance(P.maps, MutableHashTable) then error("Expected type MutableHashTable for maps, instead got type "|toString class P.maps)
)

-- PURPOSE: Make a new PolynomialOIAlgebra
-- INPUT: '(K, c, x)', a field of coefficients 'K', a positive integer 'c' of rows and a variable symbol 'x'
-- OUTPUT: A PolynomialOIAlgebra made from K, c, x
makePolynomialOIAlgebra = method(TypicalValue => PolynomialOIAlgebra, Options => {VerifyData => true})
makePolynomialOIAlgebra(Ring, ZZ, Symbol) := opts -> (K, c, x) -> (
    ret := new PolynomialOIAlgebra from {
        baseField => K,
        varRows => c, 
        varSym => x, 
        algebras => new MutableHashTable, 
        maps => new MutableHashTable};
    if opts.VerifyData then verifyData ret;
    ret
)

-- PURPOSE: Get the linearized index of a variable from its row-col position
-- INPUT: '(P, n, i, j)', a PolynomialOIAlgebra 'P', an integer 'n', a row 'i' and a column 'j'
-- OUTPUT: The index of x_(i,j) in the list of variables ordered so that in P_n we have x_(i,j) > x_(i',j') iff j > j' or j = j' and i > i'
linearFromRowCol = method(TypicalValue => ZZ, Options => {VerifyData => true})
linearFromRowCol(PolynomialOIAlgebra, ZZ, ZZ, ZZ) := opts -> (P, n, i, j) -> (
    if opts.VerifyData then scan({P, n}, verifyData);
    if n == 0 then return null;
    if i < 1 or i > P.varRows then error("Expected row between 1 and "|toString P.varRows|", instead got "|toString i);
    if j < 1 or j > n then error("Expected column between 1 and "|toString n|", instead got "|toString j);

    P.varRows * (n - j + 1) - i
)

-- PURPOSE: Get the algebra from a PolynomialOIAlgebra in a specified width
-- INPUT: '(P, n)', a PolynomialOIAlgebra 'P' and an integer 'n'
-- OUTPUT: P_n, the width n algebra of P
-- COMMENT: We use the "position down over term" monomial order and the standard ZZ-grading
getAlgebraInWidth = method(TypicalValue => PolynomialRing, Options => {VerifyData => true})
getAlgebraInWidth(PolynomialOIAlgebra, ZZ) := opts -> (P, n) -> (
    if opts.VerifyData then scan({P, n}, verifyData);

    -- Return the algebra if it already exists
    if P.algebras#?n then return P.algebras#n;

    -- Generate the variables
    local ret;
    variables := new MutableList;
    for j from 1 to n do
        for i from 1 to P.varRows do variables#(linearFromRowCol(P, n, i, j, VerifyData => false)) = P.varSym_(i, j);
    
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
getInducedAlgebraMap = method(TypicalValue => RingMap, Options => {VerifyData => true})
getInducedAlgebraMap(PolynomialOIAlgebra, OIMap) := opts -> (P, f) -> (
    if opts.VerifyData then scan({P, f}, verifyData);

    -- Return the map if it already exists
    if P.maps#?(f.Width, f.assignment) then return P.maps#(f.Width, f.assignment);
    
    -- Generate the map
    m := #f.assignment;
    n := f.Width;
    src := getAlgebraInWidth(P, m, VerifyData => false);
    targ := getAlgebraInWidth(P, n, VerifyData => false);
    subs := new List;
    for j from 1 to m do
        for i from 1 to P.varRows do subs = append(subs, src_(linearFromRowCol(P, m, i, j, VerifyData => false)) => targ_(linearFromRowCol(P, n, i, f.assignment#(j - 1), VerifyData => false)));
    
    -- Make the map
    ret := map(targ, src, subs);

    -- Store the map
    P.maps#(f.Width, f.assignment) = ret;

    ret
)

-- PURPOSE: Get the induced algebra maps between two widths
-- INPUT: '(P, m, n)', a PolynomialOIAlgebra 'P', an integer 'm' and an integer 'n'
-- OUTPUT: A list of the elements in P(Hom(m, n))
getInducedAlgebraMaps = method(TypicalValue => List, Options => {VerifyData => true})
getInducedAlgebraMaps(PolynomialOIAlgebra, ZZ, ZZ) := opts -> (P, m, n) -> (
    if opts.VerifyData then scan({P, m, n}, verifyData);
    if n < m then return {};

    -- Get the maps
    ret := new List;
    oiMaps := getOIMaps(m, n);
    for oiMap in oiMaps do ret = append(ret, getInducedAlgebraMap(P, oiMap, VerifyData => false));

    ret
)

--------------------------------------------------------------------------------
-- END: PolynomialOIAlgebra.m2 -------------------------------------------------
--------------------------------------------------------------------------------