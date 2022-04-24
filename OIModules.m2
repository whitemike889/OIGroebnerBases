-- -*- coding: utf-8 -*-

-- PURPOSE: Algorithms for computing Gröbner bases, syzygies and free resolutions for submodules of free OI-modules over Noetherian polynomial OI-algebras
-- PROGRAMMER: Michael Morrow (https://michaelmorrow.org)
-- LAST UPDATED: April 2022

newPackage("OIModules",
    Headline => "Computation in OI-modules over Noetherian OI-algebras",
    Version => "0.1",
    Date => "April 4, 2022", -- Project birthday
    Keywords => {"Commutative Algebra"},
    Authors => {
        { Name => "Michael Morrow", HomePage => "https://michaelmorrow.org", Email => "michaelhmorrow98@gmail.com" }
    },
    DebuggingMode => true,
    HomePage => "https://github.com/morrowmh/OIModules"
)

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- EXPORTS ---------------------------------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

export {
    -- From OI.m2
    "OIMap",
    "oiMap",
    "getOIMaps",

    -- From PolynomialOIAlgebras.m2
    "PolynomialOIAlgebra",
    "polynomialOIAlgebra",
    "getAlgebraInWidth",
    "getAlgebraMapsBetweenWidths",
    "Store",
    "maps",
    "varRows",
    "varSym",
    "algebras",
    "baseField",

    -- From FreeOIModules.m2
    "FreeOIModule",
    "freeOIModule",
    "getFreeModuleInWidth",
    "alg",
    "basisSym",
    "genWidths",
    "degShifts",
    "modules",
    "Shifts"
}

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- BODY ------------------------------------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

assertValid = method() -- For data validation

--------------------------------------------------------------------------------
-- FROM: OI.m2 -----------------------------------------------------------------
--------------------------------------------------------------------------------

-- PURPOSE: Check if a given integer is nonnegative
-- INPUT: An integer 'n'
-- OUTPUT: Nothing if 0 ≤ n, otherwise error
assertNonNeg = method()
assertNonNeg ZZ := n -> if n < 0 then error("Expected a nonnegative integer, instead got "|toString(n))

-- PURPOSE: Define the new type OIMap
-- COMMENT: Should be of the form '{n, {...}}' where n is the target width and {...} is a (possibly empty) list of strictly increasing positive integers between 1 and n
OIMap = new Type of List

-- PURPOSE: Check if a given OIMap is valid
-- INPUT: An OIMap 'f'
-- OUTPUT: Nothing if f is a valid OI-map, otherwise error
assertValid OIMap := f -> (
    if not #f == 2 or not instance(f#0, ZZ) or not instance(f#1, List) then error("Expected a list of the form {n, {...}} where n is a nonnegative integer and {...} is a (possibly empty) list of strictly increasing positive integers between 1 and n, instead got "|toString(f));
    assertNonNeg f#0;

    bad := false;
    for i to #(f#1) - 1 do (
        if not instance((f#1)#i, ZZ) or (f#1)#i < 1 or (f#1)#i > f#0 then (bad = true; break); -- Check that the entries are between 1 and f#0
        if not i == 0 then if (f#1)#i <= (f#1)#(i - 1) then (bad = true; break) -- Check that the entries are strictly increasing
    );

    if bad then error("Expected a list of strictly increasing positive integers between 1 and "|toString(f#0)|", not "|toString(f#1))
)

-- PURPOSE: Make a new OIMap
-- INPUT: '(n, L)', a width 'n' and a list 'L'
-- OUTPUT: An OIMap made from n and L
oiMap = method(TypicalValue => OIMap)
oiMap(ZZ, List) := (n, L) -> (
    f := new OIMap from {n, L};
    assertValid f;
    f
)

-- PURPOSE: Get all OI-maps between two widths
-- INPUT: '(m, n)', a width 'm' and a width 'n'
-- OUTPUT: A list of the OI-maps from m to n
-- COMMENT: Returns the empty list if n < m
getOIMaps = method(TypicalValue => List)
getOIMaps(ZZ, ZZ) := (m, n) -> (
    scan({m, n}, assertNonNeg);
    if n < m then return {};

    -- Generate OI-maps
    ret := new List;
    sets := subsets(set(toList(1..n)), m);
    for s in sets do ret = append(ret, oiMap(n, sort(toList(s))));

    ret
)

--------------------------------------------------------------------------------
-- FROM: PolynomialOIAlgebras.m2 -----------------------------------------------
--------------------------------------------------------------------------------

-- Define the new type PolynomialOIAlgebra
PolynomialOIAlgebra = new Type of HashTable
toString PolynomialOIAlgebra := P -> "baseField: "|toString(P.baseField)|", varRows: "|toString(P.varRows)|", varSym: "|toString(P.varSym)
net PolynomialOIAlgebra := P -> (
    "Base field: "|net(P.baseField) ||
    "Number of variable rows: "|net(P.varRows) ||
    "Variable symbol: "|net(P.varSym)
)

-- PURPOSE: Check if a given PolynomialOIAlgebra object is valid
-- INPUT: A PolynomialOIAlgebra 'P'
-- OUTPUT: Nothing if P is a valid PolynomialOIAlgebra object, otherwise error
assertValid PolynomialOIAlgebra := P -> (
    if not sort keys P == sort {symbol baseField, symbol varRows, symbol varSym, symbol algebras, symbol maps} or not (instance(P.algebras, MutableHashTable) and instance(P.maps, MutableHashTable)) then error "Invalid PolynomialOIAlgebra HashTable keys";
    if not instance(P.baseField, Ring) or not isField P.baseField then error("Expected a field, instead got "|toString(P.baseField));
    if not instance(P.varRows, ZZ) or P.varRows < 1 then error("Expected a positive integer row count, instead got "|toString(P.varRows));
    if not instance(P.varSym, Symbol) then error("Expected variable symbol, instead got "|toString(P.varSym))
)

-- PURPOSE: Make a new PolynomialOIAlgebra
-- INPUT: '(K, c, x)', a field of coefficients 'K', a positive integer 'c' of rows and a variable symbol 'x'
-- OUTPUT: A PolynomialOIAlgebra made from K, c, x
polynomialOIAlgebra = method(TypicalValue => PolynomialOIAlgebra)
polynomialOIAlgebra(Ring, ZZ, Symbol) := (K, c, x) -> (
    P := new PolynomialOIAlgebra from {symbol baseField => K, symbol varRows => c, symbol varSym => x, symbol algebras => new MutableHashTable, symbol maps => new MutableHashTable};
    assertValid P;
    P
)

-- PURPOSE: Get the linearized index of a variable from its row-col position
-- INPUT: '(P, n, i, j)', a PolynomialOIAlgebra 'P', a width 'n', a row 'i' and a column 'j'
-- OUTPUT: The index of x_(i,j) in the list of variables ordered so that in P_n we have x_(i,j) > x_(i',j') iff j > j' or j = j' and i > i'
linearFromRowCol = method(TypicalValue => ZZ)
linearFromRowCol(PolynomialOIAlgebra, ZZ, ZZ, ZZ) := (P, n, i, j) -> (
    assertValid P;
    assertNonNeg n;
    if n == 0 then return null;
    if i < 1 or i > P.varRows then error("Expected row between 1 and "|toString(P.varRows)|", instead got "|toString(i));
    if j < 1 or j > n then error("Expected column between 1 and "|toString(n)|", instead got "|toString(j));

    P.varRows * (n - j + 1) - i
)

-- PURPOSE: Get the algebra from a PolynomialOIAlgebra in a specified width
-- INPUT: '(P, n)', a PolynomialOIAlgebra 'P' and a width 'n'
-- OUTPUT: P_n, the width n algebra of P
-- COMMENT: We use the "position down over term" monomial order and the standard ZZ-grading
-- COMMENT: "Store => false" will not store the algebra in memory (useful for large computations)
getAlgebraInWidth = method(TypicalValue => PolynomialRing, Options => {Store => true})
getAlgebraInWidth(PolynomialOIAlgebra, ZZ) := opts -> (P, n) -> (
    assertValid P;
    assertNonNeg n;
    if not instance(opts.Store, Boolean) then error("Expected boolean value for Store option, instead got "|toString(opts.Store));

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

-- PURPOSE: Get the maps between two algebras in a PolynomialOIAlgebra
-- INPUT: '(P, m, n)', a PolynomialOIAlgebra 'P', a width 'm' and a width 'n' with m ≤ n
-- OUTPUT: A list of the "OI-induced" algebra maps between P_m and P_n, i.e. P(Hom(m, n))
-- COMMENT: "Store => false" will not store the maps in memory (useful for large computations)
getAlgebraMapsBetweenWidths = method(TypicalValue => List, Options => {Store => true})
getAlgebraMapsBetweenWidths(PolynomialOIAlgebra, ZZ, ZZ) := opts -> (P, m, n) -> (
    assertValid P;
    scan({m, n}, assertNonNeg);
    if n < m then error("Expected m ≤ n, instead got m = "|toString(m)|" and n = "|toString(n));
    if not instance(opts.Store, Boolean) then error("Expected boolean value for Store option, instead got "|toString(opts.Store));

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
-- FROM: FreeOIModules.m2 ------------------------------------------------------
--------------------------------------------------------------------------------

-- Define the new type FreeOIModule
-- COMMENT: The lengths of genWidths and degShifts need to be the same
FreeOIModule = new Type of HashTable
net FreeOIModule := F -> (
    "Polynomial OI-Algebra: "|net(toString(F.alg)) ||
    "Basis symbol: "|net(toString(F.basisSym)) ||
    "Generator widths: "|net(toString(F.genWidths)) ||
    "Degree shifts: "|net(toString(F.degShifts))
)

-- PURPOSE: Check if a given FreeOIModule object is valid
-- INPUT: A FreeOIModule 'F'
-- OUTPUT: Nothing if F is a valid FreeOIModule object, otherwise error
assertValid FreeOIModule := F -> (
    if not sort keys F == sort {symbol alg, symbol basisSym, symbol genWidths, symbol degShifts, symbol modules, symbol maps} or not (instance(F.modules, MutableHashTable) and instance(F.maps, MutableHashTable)) then error "Invalid FreeOIModule HashTable keys";
    if not instance(F.alg, PolynomialOIAlgebra) then error("Expected PolynomialOIAlgebra, not "|toString(F.alg));
    assertValid F.alg;

    if not instance(F.basisSym, Symbol) then error("Expected basis symbol, not "|toString(F.basisSym));

    if not instance(F.genWidths, List) then error("Expected type List for genWidths, not "|toString(class(F.genWidths)));
    for l in F.genWidths do if not instance(l, ZZ) then error("Expected a list of integers for genWidths, not "|toString(F.genWidths));

    if not instance(F.degShifts, List) then error("Expected type List for degShifts, not "|toString(class(F.degShifts)));
    for l in F.degShifts do if not instance(l, ZZ) then error("Expected a list of integers for degShifts, not "|toString(F.degShifts));

    if not #(F.genWidths) == #(F.degShifts) then error "Length of genWidths must equal length of degShifts";
)

-- PURPOSE: Make a new FreeOIModule
-- INPUT: '(P, e, W)', a PolynomialOIAlgebra 'P', a basis symbol 'e' and a list of generator widths 'W'
-- OUTPUT: A FreeOIModule made from P, e, W
-- COMMENT: Default degree shifts are all zero
freeOIModule = method(TypicalValue => FreeOIModule, Options => {Shifts => 0})
freeOIModule(PolynomialOIAlgebra, Symbol, List) := opts -> (P, e, W) -> (
    if #W == 0 then error("Expected a non-empty list of generator widths, instead got "|toString(W));
    shifts := new MutableList;
    if opts.Shifts === 0 then for i to #W - 1 do shifts#i = 0
    else if instance(opts.Shifts, List) then for i to #(opts.Shifts) - 1 do shifts#i = (opts.Shifts)#i
    else error("Invalid shifts option: "|toString(opts.Shifts));

    ret := new FreeOIModule from {symbol alg => P, symbol basisSym => e, symbol genWidths => W, symbol degShifts => toList(shifts), symbol modules => new MutableHashTable, symbol maps => new MutableHashTable};
    assertValid ret;

    ret
)

-- PURPOSE: Get the free module from a FreeOIModule in a specified width
-- INPUT: '(F, n)', a FreeOIModule 'F' and a width 'n'
-- OUTPUT: F_n, the free module in width n
-- COMMENT: "Store => false" will not store the module in memory (useful for large computations)
getFreeModuleInWidth = method(TypicalValue => Module, Options => {Store => true})
getFreeModuleInWidth(FreeOIModule, ZZ) := opts -> (F, n) -> (
    assertValid F; assertNonNeg n;
    if not instance(opts.Store, Boolean) then error("Expected boolean value for Store option, instead got "|toString(opts.Store));

    -- Return the module if it already exists
    if (F.modules)#?n then return (F.modules)#n;

    -- Generate the degrees
    local ret;
    alg := getAlgebraInWidth(F.alg, n, Store => opts.Store);
    degList := new List;
    for i to #(F.genWidths) - 1 do degList = append(degList, binomial(n, (F.genWidths)#i) : (F.degShifts)#i);

    -- Make the module
    ret = alg^degList;

    -- Store the module
    if opts.Store then (F.modules)#n = ret;

    ret
)

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- DOCUMENTATION ---------------------------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

beginDocumentation()

doc ///
Node
    Key
        OIModules
    Headline
        Computation in OI-modules over Noetherian polynomial OI-algebras
    Description
        Text
            This package allows one to compute Gröbner bases, syzygies and free resolutions for submodules of free OI-modules over Noetherian polynomial OI-algebras.
///

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- TESTS -----------------------------------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------



end