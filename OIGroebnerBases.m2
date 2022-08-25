-- -*- coding: utf-8 -*-

-- PURPOSE: Algorithms for computing Gröbner bases, syzygies and free resolutions for submodules of free OI-modules over Noetherian polynomial OI-algebras
-- PROGRAMMER: Michael Morrow
-- COMMENT: This package was made using Macaulay2-Package-Template, available here: https://github.com/morrowmh/Macaulay2-Package-Template

newPackage("OIGroebnerBases",
    Headline => "Computation in OI-modules over Noetherian polynomial OI-algebras",
    Version => "2.0.0-dev",
    Date => "April 4, 2022", -- Project birthday
    Keywords => { "Commutative Algebra" },
    Authors => {
        { Name => "Michael Morrow", HomePage => "https://michaelmorrow.org", Email => "michaelhmorrow98@gmail.com" }
    },
    DebuggingMode => true,
    HomePage => "https://github.com/morrowmh/OIGroebnerBases"
)

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- EXPORT AND PROTECT ----------------------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

export {
    -- Types
    "OIMap",
    "PolynomialOIAlgebra",

    -- Methods
    "makeOIMap", "getOIMaps", "composeOIMaps",
    "makePolynomialOIAlgebra", "getAlgebraInWidth", "getInducedAlgebraMap"
}

scan({
    -- Keys
    targWidth, img,
    baseField, varRows, varSym, varOrder, algebras, maps
}, protect)

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- BODY ------------------------------------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

-- Cache for storing OI-maps
oiMapCache = new MutableHashTable

-- Should be of the form {targWidth => ZZ, img => List}
OIMap = new Type of HashTable

net OIMap := f -> "Source: ["|net(#f.img)|"] Target: ["|net f.targWidth|"]" || "Image: "|net f.img

source OIMap := f -> toList(1..#f.img)
target OIMap := f -> toList(1..f.targWidth)
image OIMap := f -> f.img

-- Given an OI-map f, compute f(n)
OIMap ZZ := (f, n) -> f.img#(n - 1)

makeOIMap = method(TypicalValue => OIMap)
makeOIMap(ZZ, List) := (n, L) -> new OIMap from {targWidth => n, img => L}

-- Get the OI-maps between two widths
getOIMaps = method(TypicalValue => List)
getOIMaps(ZZ, ZZ) := (m, n) -> (
    if n < m then return {};
    
    -- Return the maps if they already exist
    if oiMapCache#?(m, n) then return oiMapCache#(m, n);

    sets := subsets(toList(1..n), m);
    ret := for i to #sets - 1 list new OIMap from {targWidth => n, img => sets#i};

    -- Store the maps
    oiMapCache#(m, n) = ret;

    ret
)

-- Given OI-maps f and g, compute f(g)
composeOIMaps = method(TypicalValue => OIMap)
composeOIMaps(OIMap, OIMap) := (f, g) -> (
    if not source f === target g then error "Maps cannot be composed due to incompatible source and target";
    L := for i in source g list f g i;
    new OIMap from {targWidth => f.targWidth, img => L}
)

-- Shorthand composition
OIMap OIMap := (f, g) -> composeOIMaps(f, g)

-- Should be of the form {baseField => Ring, varRows => ZZ, varSym => Symbol, varOrder => Symbol, algebras => MutableHashTable, maps => MutableHashTable}
PolynomialOIAlgebra = new Type of HashTable

toString PolynomialOIAlgebra := P -> "("|toString P.baseField|", "|toString P.varRows|", "|toString P.varSym|", "|toString P.varOrder|")"

net PolynomialOIAlgebra := P -> "Base field: "|net P.baseField ||
    "Number of variable rows: "|net P.varRows ||
    "Variable symbol: "|net P.varSym ||
    "Variable order: "|net P.varOrder

makePolynomialOIAlgebra = method(TypicalValue => PolynomialOIAlgebra)
makePolynomialOIAlgebra(Ring, ZZ, Symbol, Symbol) := (K, c, x, v) ->
    new PolynomialOIAlgebra from {
        baseField => K,
        varRows => c,
        varSym => x,
        varOrder => v,
        algebras => new MutableHashTable,
        maps => new MutableHashTable}

-- Get the linearized variable index
-- Expects (PolynomialOIAlgebra, ZZ, ZZ, ZZ)
linearFromRowCol := (P, n, i, j) -> P.varRows * (n - j + 1) - i

getAlgebraInWidth = method(TypicalValue => PolynomialRing)
getAlgebraInWidth(PolynomialOIAlgebra, ZZ) := (P, n) -> (
    -- Return the algebra if it already exists
    if P.algebras#?n then ( use P.algebras#n; return P.algebras#n );

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

-- Shorthand for getAlgebraInWidth
PolynomialOIAlgebra _ ZZ := (P, n) -> getAlgebraInWidth(P, n)

-- Get the algebra map induced by an OI-map
getInducedAlgebraMap = method(TypicalValue => RingMap)
getInducedAlgebraMap(PolynomialOIAlgebra, OIMap) := (P, f) -> (
    -- Return the map if it already exists
    if P.maps#?f then return P.maps#f;
    
    -- Generate the assignment
    m := #f.img;
    n := f.targWidth;
    src := P_m;
    targ := P_n;
    subs := flatten for j from 1 to m list
        for i from 1 to P.varRows list src_(linearFromRowCol(P, m, i, j)) => targ_(linearFromRowCol(P, n, i, f j));
    
    -- Make the map
    ret := map(targ, src, subs);

    -- Store the map
    P.maps#f = ret;

    ret
)

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- DOCUMENTATION ---------------------------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

beginDocumentation()

-- load "Documentation.m2"

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- TESTS -----------------------------------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------



end

-- Scratch work
load "OIGroebnerBases.m2"
P = makePolynomialOIAlgebra(QQ, 3, x, BLAH)
f = getInducedAlgebraMap(P, makeOIMap(5, {2,3,5}))