-- -*- coding: utf-8 -*-

-- PURPOSE: Algorithms for computing Gröbner bases, syzygies and free resolutions for submodules of free OI-modules over Noetherian polynomial OI-algebras
-- PROGRAMMER: Michael Morrow (https://michaelmorrow.org)
-- LAST UPDATED: May 2022
-- COMMENT: This package was made using Macualay2-Package-Template, available here: https://github.com/morrowmh/Macaulay2-Package-Template

newPackage("OIModules",
    Headline => "Computation in OI-modules over Noetherian OI-algebras",
    Version => "0.1",
    Date => "April 4, 2022", -- Project birthday
    Keywords => { "Commutative Algebra" },
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
    -- From OIModules.m2 ---------------
    ------------------------------------

    -- Methods
    "assertValid",

    -- Options
    "AssertValid",

    ------------------------------------
    -- From OIMap.m2 -------------------
    ------------------------------------

    -- Types
    "OIMap",

    -- Methods
    "makeOIMap",
    "getOIMaps",

    -- Keys
    "Width",
    "assignment",

    ------------------------------------
    -- From PolynomialOIAlgebra.m2 -----
    ------------------------------------
    
    -- Types
    "PolynomialOIAlgebra",

    -- Methods
    "makePolynomialOIAlgebra",
    "getAlgebraInWidth",
    "linearFromRowCol",
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
    "makeSchreyerMonomialOrder",
    "installSchreyerMonomialOrder",

    -- Keys
    "srcMod",
    "targMod",
    "schreyerList",

    ------------------------------------
    -- From TermsAndMonomials.m2 -------
    ------------------------------------

    -- Types
    "BasisIndex",
    "OITerm",
    "OIMonomial",
    "OIBasisElement",

    -- Methods
    "makeBasisIndex",
    "makeOITerm",
    "makeOIMonomial",
    "makeOIBasisElement",
    "getOIBasisElementsInWidth",

    -- Keys
    "freeOIMod",
    "idx",
    "oiMap",
    "ringElement",
    "basisIndex",

    ------------------------------------
    -- From FreeOIModule.m2 ------------
    ------------------------------------

    -- Types
    "FreeOIModule",

    -- Methods
    "makeFreeOIModule",
    "getFreeModuleInWidth",
    "freeOIModuleFromElement",
    "widthOfElement",

    -- Options
    "DegreeShifts",
    "UpdateBasis",

    -- Keys
    "polyOIAlg",
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
-- BEGIN: OIMap.m2 -------------------------------------------------------------
--------------------------------------------------------------------------------

-- PURPOSE: Check if a given integer is nonnegative
-- INPUT: An integer 'n'
-- OUTPUT: Nothing if 0 ≤ n, otherwise error
assertValid ZZ := n -> if n < 0 then error("Expected a nonnegative integer, instead got "|toString n)

-- PURPOSE: Define the new type OIMap
-- COMMENT: Should be of the form {Width => ZZ, assignment => List}
OIMap = new Type of HashTable

-- Install toString method for OIMap
toString OIMap := f -> toString new List from {f.Width, f.assignment}

-- Install net method for OIMap
net OIMap := f -> "Width: "|net f.Width || "Assignment: "|net f.assignment

-- Validation method for OIMap
assertValid OIMap := f -> (
    if not sort keys f === sort {Width, assignment} then error("Expected keys {Width, assignment}, instead got "|toString keys f);
    if not instance(f.Width, ZZ) then error("Expected type ZZ for Width, instead got type "|toString class f.Width); 
    assertValid f.Width;

    bad := false;
    for i to #f.assignment - 1 do (
        entry := f.assignment#i;
        if not instance(entry, ZZ) or entry < 1 or entry > f.Width then ( bad = true; break ); -- Check that the entries are between 1 and f.Width
        if not i == 0 then if entry <= f.assignment#(i - 1) then ( bad = true; break ) -- Check that the entries are strictly increasing
    );

    if bad then error("Expected a list of strictly increasing positive integers between 1 and "|toString f.Width|", instead got "|toString f.assignment)
)

-- PURPOSE: Make a new OIMap
-- INPUT: '(n, L)', a width 'n' and a list 'L'
-- OUTPUT: An OIMap made from n and L
makeOIMap = method(TypicalValue => OIMap, Options => {AssertValid => true})
makeOIMap(ZZ, List) := opts -> (n, L) -> (
    f := new OIMap from {Width => n, assignment => L};
    if opts.AssertValid then assertValid f;
    f
)

-- PURPOSE: Get all OI-maps between two widths
-- INPUT: '(m, n)', a width 'm' and a width 'n'
-- OUTPUT: A list of the OI-maps from m to n
-- COMMENT: Returns the empty list if n < m
getOIMaps = method(TypicalValue => List, Options => {AssertValid => true})
getOIMaps(ZZ, ZZ) := opts -> (m, n) -> (
    if opts.AssertValid then scan({m, n}, assertValid);
    if n < m then return {};

    -- Generate OI-maps
    ret := new List;
    sets := subsets(set toList(1..n), m);
    for s in sets do ret = append(ret, makeOIMap(n, sort toList s));

    ret
)

--------------------------------------------------------------------------------
-- END: OIMap.m2 ---------------------------------------------------------------
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- BEGIN: PolynomialOIAlgebra.m2 -----------------------------------------------
--------------------------------------------------------------------------------

-- Define the new type PolynomialOIAlgebra
-- COMMENT: Should be of the form {baseField => Ring, varRows => ZZ, varSym => Symbol, algebras => MutableHashTable, maps => MutableHashTable}
PolynomialOIAlgebra = new Type of HashTable

-- Install toString method for PolynomialOIAlgebra
toString PolynomialOIAlgebra := P -> "base field = "|toString P.baseField |", variable rows = "|toString P.varRows|", variable symbol = "|toString P.varSym

-- Install net method for PolynomialOIAlgebra
net PolynomialOIAlgebra := P -> "Base field: "|net P.baseField ||
    "Number of variable rows: "|net P.varRows ||
    "Variable symbol: "|net P.varSym

-- Validation method for PolynomialOIAlgebra
assertValid PolynomialOIAlgebra := P -> (
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
makePolynomialOIAlgebra = method(TypicalValue => PolynomialOIAlgebra, Options => {AssertValid => true})
makePolynomialOIAlgebra(Ring, ZZ, Symbol) := opts -> (K, c, x) -> (
    P := new PolynomialOIAlgebra from {
        baseField => K,
        varRows => c, 
        varSym => x, 
        algebras => new MutableHashTable, 
        maps => new MutableHashTable};
    if opts.AssertValid then assertValid P;
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
getAlgebraInWidth = method(TypicalValue => PolynomialRing, Options => {Store => true, AssertValid => true})
getAlgebraInWidth(PolynomialOIAlgebra, ZZ) := opts -> (P, n) -> (
    if opts.AssertValid then scan({P, n}, assertValid);
    if not instance(opts.Store, Boolean) then error("Expected boolean value for Store option, instead got "|toString opts.Store);

    -- Return the algebra if it already exists
    if P.algebras#?n then return P.algebras#n;

    -- Generate the variables
    local ret;
    variables := new MutableList;
    for j from 1 to n do
        for i from 1 to P.varRows do variables#(linearFromRowCol(P, n, i, j)) = P.varSym_(i, j);
    
    -- Make a new algebra
    ret = P.baseField[variables, Degrees => {#variables:1}, MonomialOrder => {Position => Down, Lex}];

    -- Store the algebra
    if opts.Store then P.algebras#n = ret;

    ret
)

-- PURPOSE: Subscript version of getAlgebraInWidth
PolynomialOIAlgebra _ ZZ := (P, n) -> getAlgebraInWidth(P, n)

-- PURPOSE: Get the maps between two algebras in a PolynomialOIAlgebra
-- INPUT: '(P, m, n)', a PolynomialOIAlgebra 'P', a width 'm' and a width 'n'
-- OUTPUT: A list of the "OI-induced" algebra maps between P_m and P_n, i.e. P(Hom(m, n))
-- COMMENT: "Store => false" will not store the maps in memory (useful for large computations)
getAlgebraMapsBetweenWidths = method(TypicalValue => List, Options => {Store => true, AssertValid => true})
getAlgebraMapsBetweenWidths(PolynomialOIAlgebra, ZZ, ZZ) := opts -> (P, m, n) -> (
    if opts.AssertValid then scan({P, m, n}, assertValid);
    if n < m then error("Expected m ≤ n, instead got m = "|toString m|" and n = "|toString n);
    if not instance(opts.Store, Boolean) then error("Expected boolean value for Store option, instead got "|toString opts.Store);

    -- Return the maps if they already exist
    if P.maps#?(m, n) then return P.maps#(m, n);

    targ := getAlgebraInWidth(P, n, Store => opts.Store);
    src := getAlgebraInWidth(P, m, Store => opts.Store);

    local ret;
    algMaps := new List;
    oiMaps := getOIMaps(m, n);

    -- Generate algebra maps
    for oiMap in oiMaps do (
        subs := new List;

        for j from 1 to m do
            for i from 1 to P.varRows do subs = append(subs, src_(linearFromRowCol(P, m, i, j)) => targ_(linearFromRowCol(P, n, i, oiMap.assignment#(j - 1))));

        algMaps = append(algMaps, map(targ, src, subs))
    );
    ret = algMaps;

    -- Store the maps
    if opts.Store then P.maps#(m, n) = ret;

    ret
)

--------------------------------------------------------------------------------
-- END: PolynomialOIAlgebra.m2 -------------------------------------------------
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- BEGIN: FreeOIModule.m2 ------------------------------------------------------
--------------------------------------------------------------------------------

-- Define the new type FreeOIModule
-- COMMENT: Should be of the form {polyOIAlg => PolynomialOIAlgebra, basisSym => Symbol, genWidths => List, degShifts => List, monOrder => MutableList, modules => MutableHashTable, maps => MutableHashTable}
-- COMMENT: The lengths of genWidths and degShifts need to be the same
FreeOIModule = new Type of HashTable

-- Install net method for FreeOIModule
net FreeOIModule := F -> "Polynomial OI-algebra: "|net toString F.polyOIAlg ||
    "Basis symbol: "|net F.basisSym ||
    "Generator widths: "|net F.genWidths ||
    "Degree shifts: "|net F.degShifts ||
    "Monomial order: "|net F.monOrder#0

--------------------------------------------------------------------------------
-- BEGIN: SchreyerMonomialOrder.m2 ---------------------------------------------
--------------------------------------------------------------------------------

-- Define the new type SchreyerMonomialOrder
-- COMMENT: Should be of the form {srcMod => FreeOIModule, targMod => FreeOIModule, schreyerList => List}
SchreyerMonomialOrder = new Type of HashTable

-- Install net method for SchreyerMonomialOrder

-- Validation method for SchreyerMonomialOrder
assertValid SchreyerMonomialOrder := S -> (
    if not sort keys S === sort {srcMod, targMod, schreyerList} then error("Expected keys {srcMod, targMod, schreyerList}, instead got "|toString keys S);
    if not instance(S.srcMod, FreeOIModule) or not instance(S.targMod, FreeOIModule) then error("Expected type FreeOIModule for srcMod and targMod, instead got types "|toString class S.srcMod|" and "|toString class S.targMod);
    if S.srcMod === S.targMod then error "srcMod cannot equal targMod";
    scan({S.srcMod, S.targMod}, assertValid);
    
    if not instance(S.schreyerList, List) or #S.schreyerList == 0 then error("Expected nonempty List for schreyerList, instead got "|toString S.schreyerList);
    for i to #S.schreyerList - 1 do (
        elt := S.schreyerList#i;
        if not instance(elt, Vector) then error("Expected a Vector, instead got "|toString elt);

        Width := widthOfElement elt;
        freeOIMod := freeOIModuleFromElement elt;

        if not class elt === getFreeModuleInWidth(freeOIMod, Width, UpdateBasis => false) then error("Element "|toString i|" of schreyerList does not belong to its specified free OI-module in width "|toString Width);
        if not Width == S.srcMod.genWidths#i then error("Element "|toString i|" of schreyerList has width "|toString Width|" which does not match srcMod.genWidths#"|toString i|" = "|toString S.srcMod.genWidths#i)
    )
)

-- PURPOSE: Make a new SchreyerMonomialOrder
-- INPUT: '(G, F, L)', a FreeOIModule 'G', a FreeOIModule 'F' and a  List 'L' of elements of G
-- OUTPUT: A SchreyerMonomialOrder made from G, F and L
makeSchreyerMonomialOrder = method(TypicalValue => SchreyerMonomialOrder, Options => {AssertValid => true})
makeSchreyerMonomialOrder(FreeOIModule, FreeOIModule, List) := opts -> (G, F, L) -> (
    ret := new SchreyerMonomialOrder from {targMod => G, srcMod => F, schreyerList => L};
    if opts.AssertValid then assertValid ret;
    ret
)

-- PURPOSE: Install a SchreyerMonomialOrder on its source module
-- INPUT: A SchreyerMonomialOrder 'S'
-- OUTPUT: If S is a valid SchreyerMonomialOrder, sets S.srcMod.monOrder#0 to S
installSchreyerMonomialOrder = method(Options => {AssertValid => true})
installSchreyerMonomialOrder SchreyerMonomialOrder := opts -> S -> (
    if opts.AssertValid then assertValid S;
    S.srcMod.monOrder#0 = S
)

--------------------------------------------------------------------------------
-- END: SchreyerMonomialOrder.m2 -----------------------------------------------
--------------------------------------------------------------------------------

-- Validation method for FreeOIModule
assertValid FreeOIModule := F -> (
    if not sort keys F === sort {polyOIAlg, basisSym, genWidths, degShifts, monOrder, modules, maps} then error("Expected keys {polyOIAlg, basisSym, genWidths, degShifts, monOrder, modules, maps}, instead got "|toString keys F);
    if not instance(F.polyOIAlg, PolynomialOIAlgebra) then error("Expected type PolynomialOIAlgebra for polyOIAlg, instead got type "|toString class F.polyOIAlg);
    assertValid F.polyOIAlg;

    if not instance(F.modules, MutableHashTable) then error("Expected type MutableHashTable for modules, instead got type "|toString class F.modules);
    if not instance(F.maps, MutableHashTable) then error("Expected type MutableHashTable for maps, instead got type "|toString class F.maps);
    if not instance(F.basisSym, Symbol) then error("Expected type Symbol for basisSym, instead got type "|toString class F.basisSym);

    if not instance(F.genWidths, List) then error("Expected type List for genWidths, instead got type "|toString class F.genWidths);
    for l in F.genWidths do if not instance(l, ZZ) then error("Expected a list of integers for genWidths, instead got "|toString F.genWidths);

    if not instance(F.degShifts, List) then error("Expected type List for degShifts, instead got type "|toString class F.degShifts);
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
makeFreeOIModule = method(TypicalValue => FreeOIModule, Options => {DegreeShifts => null, AssertValid => true})
makeFreeOIModule(PolynomialOIAlgebra, Symbol, List) := opts -> (P, e, W) -> (
    if #W == 0 then error("Expected a non-empty list of generator widths, instead got "|toString W);
    
    local shifts;
    if opts.DegreeShifts === null then shifts = #W : 0
    else if instance(opts.DegreeShifts, List) then shifts = opts.DegreeShifts
    else error("Invalid DegreeShifts option: "|toString opts.DegreeShifts);

    ret := new FreeOIModule from {
        polyOIAlg => P,
        basisSym => e,
        genWidths => W,
        degShifts => toList shifts,
        monOrder => new MutableList from {Lex},
        modules => new MutableHashTable,
        maps => new MutableHashTable};
    if opts.AssertValid then assertValid ret;

    ret
)

--------------------------------------------------------------------------------
-- BEGIN: TermsAndMonomials.m2 -------------------------------------------------
--------------------------------------------------------------------------------

-- Define the new type BasisIndex
-- COMMENT: Should be of the form {freeOIMod => FreeOIModule, oiMap => OIMap, idx => ZZ}
-- COMMENT: idx should be from 1 to #freeOIMod.genWidths and oiMap should be a map with source freeOIMod.genWidths#(idx - 1)
BasisIndex = new Type of HashTable

-- PURPOSE: Make a new BasisIndex
-- INPUT: '(F, f, i)', a FreeOIModule 'F', an OIMap 'f' and an index 'i'
-- OUTPUT: A BasisIndex made from F, f and i
makeBasisIndex = method(TypicalValue => BasisIndex, Options => {AssertValid => true})
makeBasisIndex(FreeOIModule, OIMap, ZZ) := opts -> (F, f, i) -> (
    ret := new BasisIndex from {freeOIMod => F, oiMap => f, idx => i};
    if opts.AssertValid then assertValid ret;
    ret
)

-- Validation method for BasisIndex
assertValid BasisIndex := b -> (
    if not sort keys b === sort {freeOIMod, oiMap, idx} then error("Expected keys {freeOIMod, oiMap, idx}, instead got "|toString keys b);
    if not instance(b.freeOIMod, FreeOIModule) then error("Expected type FreeOIModule for freeOIMod, instead got type "|toString class b.freeOIMod);
    if not instance(b.oiMap, OIMap) then error("Expected type OIMap for oiMap, instead got type "|toString class b.oiMap);
    if not instance(b.idx, ZZ) then error("Expected type ZZ for idx, instead got type "|toString class b.idx);
    scan({b.freeOIMod, b.oiMap}, assertValid);

    genWidths := b.freeOIMod.genWidths;
    oiMap := b.oiMap;
    assignment := oiMap.assignment;
    idx := b.idx;

    if not (idx <= #genWidths and idx >= 1) then error("Expected idx between 1 and #genWidths = "|toString #genWidths|", instead got "|toString idx);
    if not #assignment == genWidths#(idx - 1) then error("Expected OIMap with source = genWidths#"|toString(idx - 1)|", instead got "|toString oiMap)
)

-- Define the new type OITerm
-- COMMENT: Should be of the form {ringElement => RingElement, basisIndex => BasisIndex}
OITerm = new Type of HashTable

-- PURPOSE: Make a new OITerm
-- INPUT: '(elt, b)', a RingElement 'elt' and a BasisIndex 'b'
-- OUTPUT: An OITerm made from elt and b
makeOITerm = method(TypicalValue => OITerm, Options => {AssertValid => true})
makeOITerm(RingElement, BasisIndex) := opts -> (elt, b) -> (
    ret := new OITerm from {ringElement => elt, basisIndex => b};
    if opts.AssertValid then assertValid ret;
    ret
)

-- Install net method for OITerm
net OITerm := f -> net f.ringElement | net f.basisIndex.freeOIMod.basisSym_(toString f.basisIndex.oiMap, f.basisIndex.idx)

-- Validation method for OITerm
assertValid OITerm := f -> (
    if not sort keys f === sort {ringElement, basisIndex} then error("Expected keys {ringElement, basisIndex}, instead got "|toString keys f);
    if not instance(f.ringElement, RingElement) then error("Expected type RingElement for ringElement, instead got "|toString class f.ringElement);
    if not instance(f.basisIndex, BasisIndex) then error("Expected type BasisIndex for basisIndex, instead got "|toString class f.basisIndex);
    assertValid f.basisIndex;
    
    elt := f.ringElement;
    freeOIMod := f.basisIndex.freeOIMod;
    Width := f.basisIndex.oiMap.Width;

    coeffs := ring getFreeModuleInWidth(freeOIMod, Width, UpdateBasis => false); -- Or getAlgebraInWidth(freeOIMod.polyOIAlg, Width);
    if not class elt === coeffs then error("Expected element of "|toString coeffs|", instead got "|toString elt|" which is an element of "|class elt);
    if not #terms elt == 1 then error("Expected a term, instead got "|toString elt)
)

-- Define the new type OIMonomial
-- COMMENT: Should be of the form {ringElement => RingElement, basisIndex => BasisIndex}
-- COMMENT: ringElement should have coefficient 1
OIMonomial = new Type of OITerm

-- PURPOSE: Make a new OIMonomial
-- INPUT: '(elt, b)', a RingElement 'elt' and a BasisIndex 'b'
-- OUTPUT: An OIMonomial made from elt and b
makeOIMonomial = method(TypicalValue => OIMonomial, Options => {AssertValid => true})
makeOIMonomial(RingElement, BasisIndex) := opts -> (elt, b) -> (
    ret := new OIMonomial from {ringElement => elt, basisIndex => b};
    if opts.AssertValid then assertValid ret;
    ret
)

-- Validation method for OIMonomial
assertValid OIMonomial := f -> (
    assertValid new OITerm from f;
    
    elt := f.ringElement;
    baseField := f.basisIndex.freeOIMod.polyOIAlg.baseField;
    if not leadCoefficient elt == 1_baseField then error("Expected lead coefficient of 1, instead got "|toString leadCoefficient elt)
)

-- Comparison method for OIMonomial
OIMonomial ? OIMonomial := (f, g) -> (
    scan({f, g}, assertValid);
    if f === g then return symbol ==;

    eltf := f.ringElement; eltg := g.ringElement;
    bf := f.basisIndex; bg := g.basisIndex;
    oiMapf := bf.oiMap; oiMapg := bg.oiMap;
    idxf := bf.idx; idxg := bg.idx;

    if not bf.freeOIMod === bg.freeOIMod then return incomparable; -- Must belong to the same FreeOIModule
    freeOIMod := bf.freeOIMod;

    monOrder := freeOIMod.monOrder#0;
    if monOrder === Lex then ( -- LEX ORDER
        vectf := prepend(oiMapf.Width, oiMapf.assignment);
        vectg := prepend(oiMapg.Width, oiMapg.assignment);

        if not idxf == idxg then ( if idxf < idxg then return symbol > else return symbol < );
        if not vectf == vectg then return vectf ? vectg; -- Note: #vectf = #vectg since idxf = idxg
        use class eltf; -- Note: since vectf = vectg we have oiMapf.Width = oiMapg.Width and hence class eltf = class eltg
        return eltf ? eltg -- Use the lex order defined in the coefficient ring (see getAlgebraInWidth)
    )
    else if instance(monOrder, SchreyerMonomialOrder) then ( -- SCHREYER ORDER
        -- IMPLEMENT THIS
    )
    else error "Monomial order not supported"
)

-- Define the new type OIBasisElement
-- COMMENT: Should be of the form {ringElement => RingElement, basisIndex => BasisIndex}
-- COMMENT: ringElement should be 1
OIBasisElement = new Type of OIMonomial

-- PURPOSE: Make a new OIBasisElement
-- INPUT: A BasisIndex 'b'
-- OUTPUT: An OIBasisElement made from b
makeOIBasisElement = method(TypicalValue => OIBasisElement, Options => {AssertValid => true})
makeOIBasisElement BasisIndex := opts -> b -> (
    if opts.AssertValid then assertValid b;

    one := 1_(ring getFreeModuleInWidth(b.freeOIMod, b.oiMap.Width, UpdateBasis => false));
    new OIBasisElement from makeOIMonomial(one, b, AssertValid => opts.AssertValid)
)

-- Validation method for OIBasisElement
assertValid OIBasisElement := f -> (
    assertValid new OITerm from f;

    elt := f.ringElement;
    b := f.basisIndex;
    one := 1_(ring getFreeModuleInWidth(b.freeOIMod, b.oiMap.Width, UpdateBasis => false));
    if not elt === one then error("Expected ringElement = 1, instead got "|toString elt)
)

-- PURPOSE: Get the basis elements in a specified width
-- INPUT: '(F, n)', a FreeOIModule 'F' and a width 'n'
-- OUTPUT: A list of the OIBasisElements in F_n ordered from greatest to least
getOIBasisElementsInWidth = method(TypicalValue => List, Options => {AssertValid => true})
getOIBasisElementsInWidth(FreeOIModule, ZZ) := opts -> (F, n) -> (
    if opts.AssertValid then scan({F, n}, assertValid);
    ret := new List;
    
    for i to #F.genWidths - 1 do (
        oiMaps := getOIMaps(F.genWidths#i, n);
        
        for oiMap in oiMaps do ret = append(ret, makeOIBasisElement(makeBasisIndex(F, oiMap, i + 1, AssertValid => false), AssertValid => opts.AssertValid))
    );

    reverse sort ret
)

--------------------------------------------------------------------------------
-- END: TermsAndMonomials.m2 ---------------------------------------------------
--------------------------------------------------------------------------------

-- PURPOSE: Get the free module from a FreeOIModule in a specified width
-- INPUT: '(F, n)', a FreeOIModule 'F' and a width 'n'
-- OUTPUT: F_n, the width n free module of F
-- COMMENT: "Store => false" will not store the module in memory (useful for large computations)
-- COMMENT: "UpdateBasis => false" will not modify the basis elements (useful for avoiding infinite loops)
getFreeModuleInWidth = method(TypicalValue => Module, Options => {Store => true, UpdateBasis => true, AssertValid => true})
getFreeModuleInWidth(FreeOIModule, ZZ) := opts -> (F, n) -> (
    if opts.AssertValid then scan({F, n}, assertValid);
    if not instance(opts.Store, Boolean) then error("Expected boolean value for Store option, instead got "|toString opts.Store);
    if not instance(opts.UpdateBasis, Boolean) then error("Expected boolean value for UpdateBasis option, instead got "|toString opts.UpdateBasis);

    local ret;

    -- Return the module if it already exists
    if F.modules#?n then ret = F.modules#n
    else (
        -- Generate the degrees
        alg := getAlgebraInWidth(F.polyOIAlg, n, Store => opts.Store);
        degList := new List;
        for i to #F.genWidths - 1 do degList = append(degList, binomial(n, F.genWidths#i) : F.degShifts#i);

        -- Make the module
        retHash := new MutableHashTable from alg^degList;
        retHash.Width = n;
        retHash.freeOIMod = F;
        ret = new Module from retHash;
    );

    -- Update the basis elements
    if opts.UpdateBasis then (
        basisElts := getOIBasisElementsInWidth(F, n);
        for i to #basisElts - 1 do (
            basisIndex := (basisElts#i).basisIndex;
            F.basisSym_(new List from {basisIndex.oiMap.Width, basisIndex.oiMap.assignment}, basisIndex.idx) <- ret_i
        )
    );

    -- Store the module
    if opts.Store then F.modules#n = ret;

    ret
)

-- Subscript version of getFreeModuleInWidth
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
    if not c.?freeOIMod then error("Element "|toString f|" has no key freeOIMod");
    if not instance(c.freeOIMod, FreeOIModule) then error("Expected FreeOIModule, instead got "|toString c.freeOIMod);
    c.freeOIMod
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

P = makePolynomialOIAlgebra(QQ, 1, x);
F = makeFreeOIModule(P, e, {2,3})