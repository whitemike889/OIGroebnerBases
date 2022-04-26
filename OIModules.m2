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
    ------------------------------------
    -- From OI.m2 ----------------------
    ------------------------------------

    -- Types
    "OIMap",

    -- Methods
    "oiMap",
    "getOIMaps",

    ------------------------------------
    -- From PolynomialOIAlgebra.m2 -----
    ------------------------------------
    
    -- Types
    "PolynomialOIAlgebra",

    -- Methods
    "polynomialOIAlgebra",
    "getAlgebraInWidth",
    "getAlgebraMapsBetweenWidths",

    -- Options
    "Store",

    -- Keys
    "varRows",
    "varSym",
    "algebras",
    "baseField",
    "maps",

    ------------------------------------
    -- From SchreyerMonomialOrder.m2 ---
    ------------------------------------

    -- Types
    "SchreyerMonomialOrder",

    -- Methods
    "schreyerMonomialOrder",
    "installSchreyerMonomialOrder",

    -- Keys
    "srcMod",
    "targMod",
    "schreyerList",

    ------------------------------------
    -- From FreeOIModule.m2 ------------
    ------------------------------------

    -- Types
    "FreeOIModule",

    -- Methods
    "freeOIModule",
    "getFreeModuleInWidth",
    "freeOIModuleFromElement",
    "widthOfElement",

    -- Options
    "DegreeShifts",

    -- Keys
    "Width",
    "parentModule",
    "oiAlgebra",
    "basisSym",
    "genWidths",
    "degShifts",
    "monOrder",
    "modules"
}

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- BODY ------------------------------------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

assertValid = method() -- For data validation

--------------------------------------------------------------------------------
-- BEGIN: OI.m2 ----------------------------------------------------------------
--------------------------------------------------------------------------------

-- PURPOSE: Check if a given integer is nonnegative
-- INPUT: An integer 'n'
-- OUTPUT: Nothing if 0 ≤ n, otherwise error
assertValid ZZ := n -> if n < 0 then error("Expected a nonnegative integer, instead got "|toString n)

-- PURPOSE: Define the new type OIMap
-- COMMENT: Should be of the form '{n, {...}}' where n is the target width and {...} is a (possibly empty) list of strictly increasing positive integers between 1 and n
OIMap = new Type of List

-- PURPOSE: Check if a given OIMap is valid
-- INPUT: An OIMap 'f'
-- OUTPUT: Nothing if f is a valid OI-map, otherwise error
assertValid OIMap := f -> (
    if not #f == 2 or not instance(f#0, ZZ) or not instance(f#1, List) then error("Expected a list of the form {n, {...}} where n is a nonnegative integer and {...} is a (possibly empty) list of strictly increasing positive integers between 1 and n, instead got "|toString f);
    assertValid f#0;

    bad := false;
    for i to #(f#1) - 1 do (
        if not instance((f#1)#i, ZZ) or (f#1)#i < 1 or (f#1)#i > f#0 then (bad = true; break); -- Check that the entries are between 1 and f#0
        if not i == 0 then if (f#1)#i <= (f#1)#(i - 1) then (bad = true; break) -- Check that the entries are strictly increasing
    );

    if bad then error("Expected a list of strictly increasing positive integers between 1 and "|toString f#0|", not "|toString f#1)
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
    scan({m, n}, assertValid);
    if n < m then return {};

    -- Generate OI-maps
    ret := new List;
    sets := subsets(set toList(1..n), m);
    for s in sets do ret = append(ret, oiMap(n, sort toList s));

    ret
)

--------------------------------------------------------------------------------
-- END: OI.m2 ------------------------------------------------------------------
--------------------------------------------------------------------------------

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

--------------------------------------------------------------------------------
-- BEGIN: FreeOIModule.m2 ------------------------------------------------------
--------------------------------------------------------------------------------

-- Define the new type FreeOIModule
-- COMMENT: The lengths of genWidths and degShifts need to be the same
FreeOIModule = new Type of HashTable

-- Install net method for FreeOIModule
net FreeOIModule := F -> "Polynomial OI-algebra: "|net toString F.oiAlgebra ||
    "Basis symbol: "|net F.basisSym ||
    "Generator widths: "|net F.genWidths ||
    "Degree shifts: "|net F.degShifts ||
    "Monomial order: "|net F.monOrder#0

--------------------------------------------------------------------------------
-- BEGIN: SchreyerMonomialOrder.m2 ---------------------------------------------
--------------------------------------------------------------------------------

-- Define the new type SchreyerMonomialOrder
SchreyerMonomialOrder = new Type of HashTable

-- Install net method for SchreyerMonomialOrder

-- PURPOSE: Check if a given SchreyerMonomialOrder is valid
-- INPUT: A SchreyerMonomialOrder 'S'
-- OUTPUT: Nothing if S is a valid SchreyerMonomialOrder, otherwise error
assertValid SchreyerMonomialOrder := S -> (
    if not sort keys S === sort {srcMod, targMod, schreyerList} then error("Invalid SchreyerMonomialOrder HashTable keys: "|toString keys S);
    if not instance(S.srcMod, FreeOIModule) or not instance(S.targMod, FreeOIModule) then error("Expected type FreeOIModule for srcMod and targMod, instead got types "|toString class S.srcMod|" and "|toString class S.targMod);
    if S.srcMod === S.targMod then error "srcMod cannot equal targMod";
    scan({S.srcMod, S.targMod}, assertValid);
    
    if not instance(S.schreyerList, List) or #S.schreyerList == 0 then error("Expected nonempty List for schreyerList, instead got "|toString S.schreyerList);
    for i to #S.schreyerList - 1 do (
        elt := S.schreyerList#i;
        wid := widthOfElement elt;
        par := freeOIModuleFromElement elt;
        if not class elt === getFreeModuleInWidth(par, wid) then error("Element "|toString i|" of schreyerList does not belong to its specified parent OI-module in width "|toString wid);
        if not wid == (S.srcMod).genWidths#i then error("Element "|toString i|" of schreyerList has width "|toString wid|" which does not match srcMod.genWidths#i = "|toString (S.srcMod).genWidths#i)
    )
)

-- PURPOSE: Make a new SchreyerMonomialOrder
-- INPUT: '(targModArg, srcModArg, schreyerListArg)', a FreeOIModule 'targModArg', a FreeOIModule 'srcModArg' and a nonempty List 'schreyerListArg' of elements of targModArg
-- OUTPUT: A SchreyerMonomialOrder made from targModArg, srcModArg and schreyerListArg
-- COMMENT: Error if targModArg === srcModArg
schreyerMonomialOrder = method(TypicalValue => SchreyerMonomialOrder)
schreyerMonomialOrder(FreeOIModule, FreeOIModule, List) := (targModArg, srcModArg, schreyerListArg) -> (
    if targModArg === srcModArg then error "srcMod cannot equal targMod";
    if #schreyerListArg == 0 then error "Expected nonempty List for schreyerList";
    
    ret := new SchreyerMonomialOrder from {targMod => targModArg, srcMod => srcModArg, schreyerList => schreyerListArg};
    assertValid ret;
    ret
)

-- PURPOSE: Install a SchreyerMonomialOrder on its source module
-- INPUT: A SchreyerMonomialOrder 'S'
-- OUTPUT: If S is a valid SchreyerMonomialOrder, sets (S.srcMod).monOrder#0 to S
installSchreyerMonomialOrder = method()
installSchreyerMonomialOrder SchreyerMonomialOrder := S -> (
    assertValid S;
    (S.srcMod).monOrder#0 = S
)

-- Shortcut version
installSchreyerMonomialOrder(FreeOIModule, FreeOIModule, List) := (targModArg, srcModArg, schreyerListArg) -> (
    S := schreyerMonomialOrder(targModArg, srcModArg, schreyerListArg);
    (S.srcMod).monOrder#0 = S
)

--------------------------------------------------------------------------------
-- END: SchreyerMonomialOrder.m2 -----------------------------------------------
--------------------------------------------------------------------------------

-- PURPOSE: Check if a given FreeOIModule object is valid
-- INPUT: A FreeOIModule 'F'
-- OUTPUT: Nothing if F is a valid FreeOIModule object, otherwise error
assertValid FreeOIModule := F -> (
    if not sort keys F === sort {oiAlgebra, basisSym, genWidths, degShifts, monOrder, modules, maps} then error("Invalid FreeOIModule HashTable keys: "|toString keys F);
    if not instance(F.oiAlgebra, PolynomialOIAlgebra) then error("Expected PolynomialOIAlgebra, instead got "|toString F.oiAlgebra);
    assertValid F.oiAlgebra;

    if not instance(F.modules, MutableHashTable) then error("Expected type MutableHashTable for modules, instead got "|toString class F.modules);
    if not instance(F.maps, MutableHashTable) then error("Expected type MutableHashTable for maps, instead got "|toString class F.maps);
    if not instance(F.basisSym, Symbol) then error("Expected basis symbol, instead got "|toString F.basisSym);

    if not instance(F.genWidths, List) then error("Expected type List for genWidths, instead got "|toString class F.genWidths);
    for l in F.genWidths do if not instance(l, ZZ) then error("Expected a list of integers for genWidths, instead got "|toString F.genWidths);

    if not instance(F.degShifts, List) then error("Expected type List for degShifts, instead got "|toString class F.degShifts);
    for l in F.degShifts do if not instance(l, ZZ) then error("Expected a list of integers for degShifts, instead got "|toString F.degShifts);

    if not #F.genWidths == #F.degShifts then error "Length of genWidths must equal length of degShifts";
    if not instance(F.monOrder, MutableList) or not #F.monOrder == 1 then error("Expected MutableList of length 1 for monOrder, instead got "|toString F.monOrder);
    if not (F.monOrder#0 === Lex or instance(F.monOrder#0, SchreyerMonomialOrder)) then error("Expected either Lex or type SchreyerMonomialOrder for monOrder#0, instead got "|toString F.monOrder#0)
)

-- PURPOSE: Make a new FreeOIModule
-- INPUT: '(P, e, W)', a PolynomialOIAlgebra 'P', a basis symbol 'e' and a list of generator widths 'W'
-- OUTPUT: A FreeOIModule made from P, e and W
-- COMMENT: Default monomial order is Lex
-- COMMENT: Default degree shifts are all zero
freeOIModule = method(TypicalValue => FreeOIModule, Options => {DegreeShifts => null})
freeOIModule(PolynomialOIAlgebra, Symbol, List) := opts -> (P, e, W) -> (
    if #W == 0 then error("Expected a non-empty list of generator widths, instead got "|toString W);
    
    local shifts;
    if opts.DegreeShifts === null then shifts = #W : 0
    else if instance(opts.DegreeShifts, List) then shifts = opts.DegreeShifts
    else error("Invalid DegreeShifts option: "|toString opts.DegreeShifts);

    ret := new FreeOIModule from {oiAlgebra => P, basisSym => e, genWidths => W, degShifts => toList shifts, monOrder => new MutableList from {Lex}, modules => new MutableHashTable, maps => new MutableHashTable};
    assertValid ret;

    ret
)

-- PURPOSE: Get the free module from a FreeOIModule in a specified width
-- INPUT: '(F, n)', a FreeOIModule 'F' and a width 'n'
-- OUTPUT: F_n, the free module in width n
-- COMMENT: "Store => false" will not store the module in memory (useful for large computations)
getFreeModuleInWidth = method(TypicalValue => Module, Options => {Store => true})
getFreeModuleInWidth(FreeOIModule, ZZ) := opts -> (F, n) -> (
    scan({F, n}, assertValid);
    if not instance(opts.Store, Boolean) then error("Expected boolean value for Store option, instead got "|toString opts.Store);

    -- Return the module if it already exists
    if (F.modules)#?n then return (F.modules)#n;

    -- Generate the degrees
    alg := getAlgebraInWidth(F.oiAlgebra, n, Store => opts.Store);
    degList := new List;
    for i to #(F.genWidths) - 1 do degList = append(degList, binomial(n, (F.genWidths)#i) : (F.degShifts)#i);

    -- Make the module
    retHash := new MutableHashTable from alg^degList;
    retHash.Width = n;
    retHash.parentModule = F;
    ret := new Module from retHash;

    -- Store the module
    if opts.Store then (F.modules)#n = ret;

    ret
)

-- PURPOSE: Subscript version of getFreeModuleInWidth
FreeOIModule _ ZZ := (F, n) -> getFreeModuleInWidth(F, n)

-- PURPOSE: Get the width of an element
-- INPUT: A Vector 'f'
-- OUTPUT: The width of f
widthOfElement = method(TypicalValue => ZZ)
widthOfElement Vector := f -> (
    c := class f;
    if not c.?Width then error("Element "|toString f|" has no key Width");
    if not instance(c.Width, ZZ) then error("Expected integer, instead got "|toString c.Width);
    c.Width
)

-- PURPOSE: Get the FreeOIModule containing an element
-- INPUT: A Vector 'f'
-- OUTPUT: The FreeOIModule containing f
freeOIModuleFromElement = method(TypicalValue => FreeOIModule)
freeOIModuleFromElement Vector := f -> (
    c := class f;
    if not c.?parentModule then error("Element "|toString f|" has no key parentModule");
    if not instance(c.parentModule, FreeOIModule) then error("Expected FreeOIModule, instead got "|toString c.parentModule);
    c.parentModule
)

--------------------------------------------------------------------------------
-- END: FreeOIModule.m2 --------------------------------------------------------
--------------------------------------------------------------------------------

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