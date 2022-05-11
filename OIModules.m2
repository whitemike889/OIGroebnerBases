-- -*- coding: utf-8 -*-

-- PURPOSE: Algorithms for computing Gröbner bases, syzygies and free resolutions for submodules of free OI-modules over Noetherian polynomial OI-algebras
-- PROGRAMMER: Michael Morrow
-- LAST UPDATED: May 2022
-- COMMENT: This package was made using Macaulay2-Package-Template, available here: https://github.com/morrowmh/Macaulay2-Package-Template

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
    "verifyData",

    -- Options
    "VerifyData",

    ------------------------------------
    -- From OIMap.m2 -------------------
    ------------------------------------

    -- Types
    "OIMap",

    -- Methods
    "makeOIMap",
    "getOIMaps",
    "composeOIMaps",

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
    "algebraMapFromOIMap",
    "getInducedAlgebraMaps",

    -- Keys
    "varRows",
    "varSym",
    "algebras",
    "baseField",
    "maps",

    ------------------------------------
    -- From FreeOIModuleMap.m2 ---------
    ------------------------------------

    -- Types
    "FreeOIModuleMap",
    
    -- Methods
    "makeFreeOIModuleMap",

    -- Keys
    "srcMod",
    "targMod",
    "targElements",

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
    "oiMonomialFromOITerm",
    "getOITermsFromVector",
    "leadOITerm",

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
    "InducedModuleMap",

    -- Methods
    "makeFreeOIModule",
    "installSchreyerMonomialOrder",
    "getFreeModuleInWidth",
    "freeOIModuleFromElement",
    "widthOfElement",
    "installOIBasisElement",
    "installOIBasisElements",
    "getInducedModuleMap",
    "getInducedModuleMaps",

    -- Options
    "DegreeShifts",

    -- Keys
    "polyOIAlg",
    "basisSym",
    "genWidths",
    "degShifts",
    "monOrder",
    "modules",
    "oiBasisElements",
    "basisImage"
}

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- BODY ------------------------------------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

verifyData = method()

--------------------------------------------------------------------------------
-- BEGIN: OIMap.m2 -------------------------------------------------------------
--------------------------------------------------------------------------------

-- Verification method for ZZ
verifyData ZZ := n -> if n < 0 then error("Expected a nonnegative integer, instead got "|toString n)

-- PURPOSE: Define the new type OIMap
-- COMMENT: Should be of the form {Width => ZZ, assignment => List}
OIMap = new Type of HashTable
OIMap.synonym = "OI-map"

-- Install net method for OIMap
net OIMap := f -> "Width: "|net f.Width || "Assignment: "|net f.assignment

-- Verification method for OIMap
verifyData OIMap := f -> (
    if not sort keys f === sort {Width, assignment} then error("Expected keys {Width, assignment}, instead got "|toString keys f);
    if not instance(f.Width, ZZ) then error("Expected type ZZ for Width, instead got type "|toString class f.Width); 
    verifyData f.Width;

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
makeOIMap = method(TypicalValue => OIMap, Options => {VerifyData => true})
makeOIMap(ZZ, List) := opts -> (n, L) -> (
    ret := new OIMap from {Width => n, assignment => L};
    if opts.VerifyData then verifyData ret;
    ret
)

-- PURPOSE: Get all OI-maps between two widths
-- INPUT: '(m, n)', a width 'm' and a width 'n'
-- OUTPUT: A list of the OI-maps from m to n
getOIMaps = method(TypicalValue => List)
getOIMaps(ZZ, ZZ) := (m, n) -> (
    if n < m then return {};
    ret := new List;
    sets := subsets(set toList(1..n), m);
    for s in sets do ret = append(ret, makeOIMap(n, sort toList s, VerifyData => false));

    ret
)

-- PURPOSE: Compose two OI-maps
-- INPUT: '(f, g)', an OIMap 'f' and an OIMap 'g'
-- OUTPUT: The OIMap f(g)
composeOIMaps = method(TypicalValue => OIMap, Options => {VerifyData => true})
composeOIMaps(OIMap, OIMap) := opts -> (f, g) -> (
    if opts.VerifyData then scan({f, g}, verifyData);
    if not g.Width == #f.assignment then error "Maps cannot be composed due to incompatible source and target";
    L := new List;
    for i to #g.assignment - 1 do L = append(L, f.assignment#(g.assignment#i - 1));
    makeOIMap(f.Width, L, VerifyData => false)
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
    if n == 0 then return null;
    if opts.VerifyData then scan({P, n}, verifyData);
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
    if n < m then return {};
    if opts.VerifyData then scan({P, m, n}, verifyData);
    
    -- Get the maps
    ret := new List;
    oiMaps := getOIMaps(m, n);
    for oiMap in oiMaps do ret = append(ret, getInducedAlgebraMap(P, oiMap, VerifyData => false));

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
FreeOIModule = new Type of HashTable
FreeOIModule.synonym = "free OI-module"

-- Install toString method for FreeOIModule
toString FreeOIModule := F -> "genWidths = "|toString F.genWidths | ", degShifts = "|toString F.degShifts

-- Install net method for FreeOIModule
net FreeOIModule := F -> (
    local monOrderNet;
    if F.monOrder#0 === Lex then monOrderNet = net Lex;
    if instance(F.monOrder#0, FreeOIModuleMap) then monOrderNet = "Schreyer monomial order given by the FreeOIModuleMap: "|net F.monOrder#0;
    "Polynomial OI-algebra: "|toString F.polyOIAlg ||
    "Basis symbol: "|net F.basisSym ||
    "Generator widths: "|net F.genWidths ||
    "Degree shifts: "|net F.degShifts ||
    "Monomial order: "|monOrderNet
)

--------------------------------------------------------------------------------
-- BEGIN: FreeOIModuleMap.m2 ---------------------------------------------------
--------------------------------------------------------------------------------

-- Define the new type FreeOIModuleMap
-- COMMENT: Should be of the form {srcMod => FreeOIModule, targMod => FreeOIModule, targElements => List}
FreeOIModuleMap = new Type of HashTable
FreeOIModuleMap.synonym = "free OI-module map"

-- Install net method for FreeOIModuleMap
net FreeOIModuleMap := f -> "Source module: "|toString f.srcMod ||
    "Target module: "|toString f.targMod ||
    "Target elements: "|toString f.targElements

-- PURPOSE: Make a new FreeOIModuleMap
-- INPUT: '(G, F, L)', a target FreeOIModule 'G', a source FreeOIModule 'F' and a List 'L' of elements of G
-- OUTPUT: A FreeOIModuleMap made from G, F and L
makeFreeOIModuleMap = method(TypicalValue => FreeOIModuleMap, Options => {VerifyData => true})
makeFreeOIModuleMap(FreeOIModule, FreeOIModule, List) := opts -> (G, F, L) -> (
    ret := new FreeOIModuleMap from {srcMod => F, targMod => G, targElements => L};
    if opts.VerifyData then verifyData ret;
    ret
)

-- Verifcation method for FreeOIModuleMap
verifyData FreeOIModuleMap := f -> (
    if not sort keys f === sort {srcMod, targMod, targElements} then error("Expected keys {srcMod, targMod, targElements}, instead got "|toString keys f);
    if not instance(f.srcMod, FreeOIModule) or not instance(f.targMod, FreeOIModule) then error("Expected type FreeOIModule for srcMod and targMod, instead got types "|toString class f.srcMod|" and "|toString class f.targMod);
    if f.srcMod === f.targMod then error "srcMod cannot equal targMod";
    scan({f.srcMod, f.targMod}, verifyData);
    
    if not instance(f.targElements, List) or #f.targElements == 0 then error("Expected nonempty List for targElements, instead got "|toString f.targElements);
    for i to #f.targElements - 1 do (
        elt := f.targElements#i;
        if not instance(elt, Vector) then error("Expected a Vector, instead got "|toString elt);
        verifyData elt;
        
        if not (class elt).Width == f.srcMod.genWidths#i then error("Element "|toString i|" of targElements has width "|toString (class elt).Width|" which does not match srcMod.genWidths#"|toString i|" = "|toString f.srcMod.genWidths#i)
    )
)

--------------------------------------------------------------------------------
-- END: FreeOIModuleMap.m2 -----------------------------------------------------
--------------------------------------------------------------------------------

-- Verification method for FreeOIModule
verifyData FreeOIModule := F -> (
    if not sort keys F === sort {polyOIAlg, basisSym, genWidths, degShifts, monOrder, modules, maps} then error("Expected keys {polyOIAlg, basisSym, genWidths, degShifts, monOrder, modules, maps}, instead got "|toString keys F);
    if not instance(F.polyOIAlg, PolynomialOIAlgebra) then error("Expected type PolynomialOIAlgebra for polyOIAlg, instead got type "|toString class F.polyOIAlg);
    verifyData F.polyOIAlg;

    if not instance(F.modules, MutableHashTable) then error("Expected type MutableHashTable for modules, instead got type "|toString class F.modules);
    if not instance(F.maps, MutableHashTable) then error("Expected type MutableHashTable for maps, instead got type "|toString class F.maps);
    if not instance(F.basisSym, Symbol) then error("Expected type Symbol for basisSym, instead got type "|toString class F.basisSym);

    if not instance(F.genWidths, List) then error("Expected type List for genWidths, instead got type "|toString class F.genWidths);
    for l in F.genWidths do if not instance(l, ZZ) then error("Expected a list of integers for genWidths, instead got "|toString F.genWidths);

    if not instance(F.degShifts, List) then error("Expected type List for degShifts, instead got type "|toString class F.degShifts);
    for l in F.degShifts do if not instance(l, ZZ) then error("Expected a list of integers for degShifts, instead got "|toString F.degShifts);

    if not #F.genWidths == #F.degShifts then error "Length of genWidths must equal length of degShifts";
    if not instance(F.monOrder, MutableList) or not #F.monOrder == 1 then error("Expected MutableList of length 1 for monOrder, instead got "|toString F.monOrder);
    if not (F.monOrder#0 === Lex or instance(F.monOrder#0, FreeOIModuleMap)) then error("Expected either Lex or type FreeOIModuleMap for monOrder#0, instead got "|toString F.monOrder#0)
)

-- PURPOSE: Make a new FreeOIModule
-- INPUT: '(P, e, W)', a PolynomialOIAlgebra 'P', a Symbol 'e' and a List of generator widths 'W'
-- OUTPUT: A FreeOIModule made from P, e and W
-- COMMENT: Default monomial order is Lex
-- COMMENT: Default degree shifts are all zero
makeFreeOIModule = method(TypicalValue => FreeOIModule, Options => {DegreeShifts => null, VerifyData => true})
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
    if opts.VerifyData then verifyData ret;

    ret
)

-- PURPOSE: Install a Schreyer monomial order on a FreeOIModule
-- INPUT: A FreeOIModuleMap 'f'
-- OUTPUT: Sets f.srcMod.monOrder#0 to f
installSchreyerMonomialOrder = method(Options => {VerifyData => true})
installSchreyerMonomialOrder FreeOIModuleMap := opts -> f -> (
    if opts.VerifyData then verifyData f;
    f.srcMod.monOrder#0 = f;
)

--------------------------------------------------------------------------------
-- BEGIN: TermsAndMonomials.m2 -------------------------------------------------
--------------------------------------------------------------------------------

-- Define the new type BasisIndex
-- COMMENT: Should be of the form {freeOIMod => FreeOIModule, oiMap => OIMap, idx => ZZ}
-- COMMENT: idx should be between 1 and #freeOIMod.genWidths
BasisIndex = new Type of HashTable
BasisIndex.synonym = "basis index"

-- PURPOSE: Make a new BasisIndex
-- INPUT: '(F, f, i)', a FreeOIModule 'F', an OIMap 'f' and an index 'i'
-- OUTPUT: A BasisIndex made from F, f and i
makeBasisIndex = method(TypicalValue => BasisIndex, Options => {VerifyData => true})
makeBasisIndex(FreeOIModule, OIMap, ZZ) := opts -> (F, f, i) -> (
    ret := new BasisIndex from {freeOIMod => F, oiMap => f, idx => i};
    if opts.VerifyData then verifyData ret;
    ret
)

-- Verification method for BasisIndex
verifyData BasisIndex := b -> (
    if not sort keys b === sort {freeOIMod, oiMap, idx} then error("Expected keys {freeOIMod, oiMap, idx}, instead got "|toString keys b);
    if not instance(b.freeOIMod, FreeOIModule) then error("Expected type FreeOIModule for freeOIMod, instead got type "|toString class b.freeOIMod);
    if not instance(b.oiMap, OIMap) then error("Expected type OIMap for oiMap, instead got type "|toString class b.oiMap);
    if not instance(b.idx, ZZ) then error("Expected type ZZ for idx, instead got type "|toString class b.idx);
    scan({b.freeOIMod, b.oiMap}, verifyData);

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
OITerm.synonym = "OI-term"

-- PURPOSE: Make a new OITerm
-- INPUT: '(elt, b)', a RingElement 'elt' and a BasisIndex 'b'
-- OUTPUT: An OITerm made from elt and b
makeOITerm = method(TypicalValue => OITerm, Options => {VerifyData => true})
makeOITerm(RingElement, BasisIndex) := opts -> (elt, b) -> (
    ret := new OITerm from {ringElement => elt, basisIndex => b};
    if opts.VerifyData then verifyData ret;
    ret
)

-- Install net method for OITerm
net OITerm := f -> net f.ringElement | net f.basisIndex.freeOIMod.basisSym_(toString f.basisIndex.oiMap.Width, toString f.basisIndex.oiMap.assignment, f.basisIndex.idx)

-- Verification method for OITerm
verifyData OITerm := f -> (
    if not sort keys f === sort {ringElement, basisIndex} then error("Expected keys {ringElement, basisIndex}, instead got "|toString keys f);
    if not instance(f.ringElement, RingElement) then error("Expected type RingElement for ringElement, instead got "|toString class f.ringElement);
    if not instance(f.basisIndex, BasisIndex) then error("Expected type BasisIndex for basisIndex, instead got "|toString class f.basisIndex);
    verifyData f.basisIndex;
    
    elt := f.ringElement;
    freeOIMod := f.basisIndex.freeOIMod;
    Width := f.basisIndex.oiMap.Width;

    coeffs := getAlgebraInWidth(freeOIMod.polyOIAlg, Width, VerifyData => false);
    if not class elt === coeffs then error("Expected element of "|toString coeffs|", instead got "|toString elt|" which is an element of "|class elt);
    if not #terms elt == 1 then error("Expected a term, instead got "|toString elt)
)

-- Define the new type OIMonomial
-- COMMENT: Should be of the form {ringElement => RingElement, basisIndex => BasisIndex}
OIMonomial = new Type of OITerm
OIMonomial.synonym = "OI-monomial"

-- PURPOSE: Make a new OIMonomial
-- INPUT: '(elt, b)', a RingElement 'elt' and a BasisIndex 'b'
-- OUTPUT: An OIMonomial made from elt and b
makeOIMonomial = method(TypicalValue => OIMonomial, Options => {VerifyData => true})
makeOIMonomial(RingElement, BasisIndex) := opts -> (elt, b) -> (
    ret := new OIMonomial from {ringElement => elt, basisIndex => b};
    if opts.VerifyData then verifyData ret;
    ret
)

-- Verification method for OIMonomial
verifyData OIMonomial := f -> (
    verifyData new OITerm from f;
    
    elt := f.ringElement;
    baseField := f.basisIndex.freeOIMod.polyOIAlg.baseField;
    if not leadCoefficient elt == 1_baseField then error("Expected lead coefficient of 1, instead got "|toString leadCoefficient elt)
)

-- Comparison method for OIMonomial
OIMonomial ? OIMonomial := (f, g) -> (
    if f === g then return symbol ==;

    eltf := f.ringElement; eltg := g.ringElement;
    bf := f.basisIndex; bg := g.basisIndex;
    oiMapf := bf.oiMap; oiMapg := bg.oiMap;
    idxf := bf.idx; idxg := bg.idx;

    if not bf.freeOIMod === bg.freeOIMod then return incomparable;
    freeOIMod := bf.freeOIMod;

    monOrder := freeOIMod.monOrder#0;
    if monOrder === Lex then ( -- LEX ORDER
        if not idxf == idxg then ( if idxf < idxg then return symbol > else return symbol < );
        if not oiMapf.Width == oiMapg.Width then return oiMapf.Width ? oiMapg.Width;
        if not oiMapf.assignment == oiMapg.assignment then return oiMapf.assignment ? oiMapg.assignment;

        use class eltf; -- Note: since oiMapf.Width = oiMapg.Width we have class eltf = class eltg
        return eltf ? eltg
    )
    else if instance(monOrder, FreeOIModuleMap) then ( -- SCHREYER ORDER
        -- TODO: IMPLEMENT THIS
    )
    else error "Monomial order not supported"
)

-- PURPOSE: Get the monomial component of an OITerm
-- INPUT: An OITerm 'f'
-- OUTPUT: The OIMonomial part of f
oiMonomialFromOITerm = method(TypicalValue => OIMonomial, Options => {VerifyData => true})
oiMonomialFromOITerm OITerm := opts -> f -> (
    if opts.VerifyData then verifyData f;
    ringElement := f.ringElement / leadCoefficient f.ringElement;
    makeOIMonomial(ringElement, f.basisIndex, VerifyData => false)
)

-- Comparison method for OITerm
OITerm ? OITerm := (f, g) -> return oiMonomialFromOITerm(f, VerifyData => false) ? oiMonomialFromOITerm(g, VerifyData => false)

-- Define the new type OIBasisElement
-- COMMENT: Should be of the form {ringElement => RingElement, basisIndex => BasisIndex}
OIBasisElement = new Type of OIMonomial
OIBasisElement.synonym = "OI-basis element"

-- PURPOSE: Make a new OIBasisElement
-- INPUT: A BasisIndex 'b'
-- OUTPUT: An OIBasisElement made from b
makeOIBasisElement = method(TypicalValue => OIBasisElement, Options => {VerifyData => true})
makeOIBasisElement BasisIndex := opts -> b -> (
    if opts.VerifyData then verifyData b;

    one := 1_(getAlgebraInWidth(b.freeOIMod.polyOIAlg, b.oiMap.Width, VerifyData => false));
    new OIBasisElement from makeOIMonomial(one, b, VerifyData => false)
)

-- Verification method for OIBasisElement
verifyData OIBasisElement := f -> (
    verifyData new OITerm from f;

    elt := f.ringElement;
    b := f.basisIndex;
    one := 1_(getAlgebraInWidth(b.freeOIMod.polyOIAlg, b.oiMap.Width, VerifyData => false));
    if not elt === one then error("Expected ringElement = 1, instead got "|toString elt)
)

-- PURPOSE: Convert an element from vector form to a list of OITerms
-- INPUT: A Vector 'v'
-- OUTPUT: A List of OITerms corresponding to the terms of v sorted from greatest to least
getOITermsFromVector = method(TypicalValue => List, Options => {VerifyData => true})
getOITermsFromVector Vector := opts -> v -> (
    if opts.VerifyData then verifyData v;

    freeOIMod := (class v).freeOIMod;
    Width := (class v).Width;
    freeMod := getFreeModuleInWidth(freeOIMod, Width, VerifyData => false);
    termList := new List;
    entryList := entries v;

    for i to #entryList - 1 do (
        if entryList#i == 0 then continue;

        oiBasisElement := freeMod.oiBasisElements#i;
        termList = append(termList, makeOITerm(entryList#i, oiBasisElement.basisIndex, VerifyData => false))
    );

    reverse sort termList
)

-- PURPOSE: Get the leading OITerm from a vector
-- INPUT: A Vector 'v'
-- OUTPUT: The largest OITerm in v
leadOITerm = method(TypicalValue => OITerm, Options => {VerifyData => true})
leadOITerm Vector := opts -> v -> (
    if opts.VerifyData then verifyData v;
    oiTerms := getOITermsFromVector(v, VerifyData => false);
    if #oiTerms == 0 then return {};
    oiTerms#0
)

--------------------------------------------------------------------------------
-- END: TermsAndMonomials.m2 ---------------------------------------------------
--------------------------------------------------------------------------------

-- PURPOSE: Get the free module from a FreeOIModule in a specified width
-- INPUT: '(F, n)', a FreeOIModule 'F' and a width 'n'
-- OUTPUT: F_n, the width n free module of F
getFreeModuleInWidth = method(TypicalValue => Module, Options => {VerifyData => true})
getFreeModuleInWidth(FreeOIModule, ZZ) := opts -> (F, n) -> (
    if opts.VerifyData then scan({F, n}, verifyData);

    local ret;

    -- Return the module if it already exists
    if F.modules#?n then ret = F.modules#n
    else (
        -- Generate the degrees
        alg := getAlgebraInWidth(F.polyOIAlg, n, VerifyData => false);
        degList := new List;
        for i to #F.genWidths - 1 do degList = append(degList, binomial(n, F.genWidths#i) : F.degShifts#i);

        -- Make the module
        retHash := new MutableHashTable from alg^degList;
        retHash.Width = n;
        retHash.freeOIMod = F;
        retHash.oiBasisElements = new List;
        
        -- Generate the OIBasisElements
        for i to #F.genWidths - 1 do (
            oiMaps := getOIMaps(F.genWidths#i, n);
            for oiMap in oiMaps do retHash.oiBasisElements = append(retHash.oiBasisElements, makeOIBasisElement(makeBasisIndex(F, oiMap, i + 1, VerifyData => false), VerifyData => false))
        );

        ret = new Module from retHash
    );

    -- Store the module
    F.modules#n = ret;

    ret
)

-- Subscript version of getFreeModuleInWidth
FreeOIModule _ ZZ := (F, n) -> getFreeModuleInWidth(F, n)

-- PURPOSE: Install a basis element for user input
-- OUTPUT: Sets the desired IndexedVariable to the appropriate basis vector
installOIBasisElement = method(Options => {VerifyData => true})

-- INPUT: '(F, n, f, i)', a FreeOIModule 'F', an integer 'n', a List 'f' and an index 'i'
installOIBasisElement(FreeOIModule, ZZ, List, ZZ) := opts -> (F, n, f, i) -> installOIBasisElement(F, makeOIMap(n, f, VerifyData => false), i, VerifyData => opts.VerifyData)

-- INPUT: '(F, f, i)', a FreeOIModule 'F', an OIMap 'f' and an index 'i'
installOIBasisElement(FreeOIModule, OIMap, ZZ) := opts -> (F, f, i) -> (
    oiBasisElement := makeOIBasisElement(makeBasisIndex(F, f, i, VerifyData => false), VerifyData => opts.VerifyData);
    installOIBasisElement(oiBasisElement, VerifyData => false)
)

-- INPUT: An OIBasisElement 'b'
installOIBasisElement OIBasisElement := opts -> b -> (
    if opts.VerifyData then verifyData b;
    freeOIMod := b.basisIndex.freeOIMod;
    Width := b.basisIndex.oiMap.Width;
    fmod := getFreeModuleInWidth(freeOIMod, Width, VerifyData => false);
    pos := position(fmod.oiBasisElements, elt -> elt === b);
    if pos === null then error "Specified basis element does not exist";
    freeOIMod.basisSym_(Width, b.basisIndex.oiMap.assignment, b.basisIndex.idx) <- fmod_pos;
)

-- PURPOSE: Install all OIBasisElements in a specified width
-- INPUT: '(F, n)', a FreeOIModule 'F' and a width 'n'
-- OUTPUT: Calls every installOIBasisElement() in F_n
-- COMMENT: This method is very slow for large n
installOIBasisElements = method(Options => {VerifyData => true})
installOIBasisElements(FreeOIModule, ZZ) := opts -> (F, n) -> (
    if opts.VerifyData then scan({F, n}, verifyData);
    for i to #F.genWidths - 1 do (
        oiMaps := getOIMaps(F.genWidths#i, n);
        for oiMap in oiMaps do installOIBasisElement(F, oiMap, i + 1, VerifyData => false)
    )
)

-- Verification method for Vector
verifyData Vector := f -> (
    c := class f;
    if not c.?Width then error("Element "|toString f|" has no key Width");
    if not instance(c.Width, ZZ) then error("Expected type ZZ for Width, instead got type "|toString class c.Width);
    verifyData c.Width;

    if not c.?freeOIMod then error("Element "|toString f|" has no key freeOIMod");
    if not instance(c.freeOIMod, FreeOIModule) then error("Expected type FreeOIModule for freeOIMod, instead got type "|toString class c.freeOIMod);
    verifyData c.freeOIMod;

    if not c.?oiBasisElements then error("Element "|toString f|" has no key oiBasisElements");
    if not instance(c.oiBasisElements, List) then error("Expected type List for oiBasisElements, instead got type "|toString class c.oiBasisElements);
    for oiBasisElement in c.oiBasisElements do if not instance(oiBasisElement, OIBasisElement) then error("Expected a List of OIBasisElements, instead got "|toString c.oiBasisElements);

    if not c === getFreeModuleInWidth(c.freeOIMod, c.Width, VerifyData => false) then error("Element "|toString f|" does not belong to its specified free OI-module in width "|toString c.Width)
)

-- PURPOSE: Get the width of an element
-- INPUT: A Vector 'f'
-- OUTPUT: The width of f
widthOfElement = method(TypicalValue => ZZ, Options => {VerifyData => true})
widthOfElement Vector := opts -> f -> (
    if opts.VerifyData then verifyData f;
    (class f).Width
)

-- PURPOSE: Get the FreeOIModule containing an element
-- INPUT: A Vector 'f'
-- OUTPUT: The FreeOIModule containing f
freeOIModuleFromElement = method(TypicalValue => FreeOIModule, Options => {VerifyData => true})
freeOIModuleFromElement Vector := opts -> f -> (
    if opts.VerifyData then verifyData f;
    (class f).freeOIMod
)

-- Install custom printing method for elements of free OI-modules
-- COMMENT: This should be improved eventually
oldNet = Vector # net
net Vector := f -> (
    c := class f;
    if not (c.?freeOIMod and c.?Width) then return oldNet f;
    verifyData f;

    oiTerms := getOITermsFromVector(f, VerifyData => false);
    if #oiTerms == 0 then return oldNet 0;
    if #oiTerms == 1 then return oldNet oiTerms#0;
    str := "";
    for i to #oiTerms - 2 do str = str | net oiTerms#i | " + ";
    str = str | net oiTerms#-1;
    str
)

-- Define the new type InducedModuleMap
-- COMMENT: Should be of the form {freeOIMod => FreeOIModule, basisImage => List, oiMap => OIMap}
InducedModuleMap = new Type of HashTable
InducedModuleMap.synonym = "induced module map"

-- Verification method for InducedModuleMap
verifyData InducedModuleMap := f -> (
    if not sort keys f === sort {basisImage, freeOIMod, oiMap} then error("Expected keys {freeOIMod, matrix, oiMap}, instead got "|toString keys f);
    if not instance(f.basisImage, List) then error("Expected type List for basisImage, instead got type "|toString class f.basisImage);
    for elt in f.basisImage do if not instance(elt, Vector) then error("Expected a list of Vectors for basisImage, instead got "|toString f.basisImage);
    if not instance(f.freeOIMod, FreeOIModule) then error("Expected type FreeOIModule for freeOIMod, instead got type "|toString class f.freeOIMod);
    verifyData f.freeOIMod;
    if not instance(f.oiMap, OIMap) then error("Expected type OIMap for oiMap, instead got type "|toString class f.oiMap);
    verifyData oiMap
)

-- PURPOSE: Get the InducedModuleMap from a given OIMap
-- INPUT: '(F, f)', a FreeOIModule 'F' and an OIMap 'f'
-- OUTPUT: The map F(f)
getInducedModuleMap = method(TypicalValue => InducedModuleMap, Options => {VerifyData => true})
getInducedModuleMap(FreeOIModule, OIMap) := opts -> (F, f) -> (
    if opts.VerifyData then scan({F, f}, verifyData);

    -- Return the map if it already exists
    if F.maps#?(f.Width, f.assignment) then return F.maps#(f.Width, f.assignment);

    -- Generate the map
    m := #f.assignment; n := f.Width;
    fmodm := getFreeModuleInWidth(F, m, VerifyData => false);
    fmodn := getFreeModuleInWidth(F, n, VerifyData => false);
    oiBasisElementsm := fmodm.oiBasisElements; oiBasisElementsn := fmodn.oiBasisElements;
    newOIBasisElements := new List;
    for oiBasisElementm in oiBasisElementsm do (
        newOIBasisElement := makeOIBasisElement(makeBasisIndex(F, composeOIMaps(f, oiBasisElementm.basisIndex.oiMap, VerifyData => false), oiBasisElementm.basisIndex.idx, VerifyData => false), VerifyData => false);
        pos := position(oiBasisElementsn, elt -> elt === newOIBasisElement);
        newOIBasisElements = append(newOIBasisElements, fmodn_pos)
    );

    -- Make the map
    ret := new InducedModuleMap from {freeOIMod => F, basisImage => newOIBasisElements, oiMap => f};

    -- Store the map
    F.maps#(f.Width, f.assignment) = ret;

    ret
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

-- Scratch work section

load "OIModules.m2"
P = makePolynomialOIAlgebra(QQ, 1, x);
F = makeFreeOIModule(P, e, {2,3});
F_5;
f = x_(1,5)*(F_5)_10 + x_(1,3)^2*(F_5)_2;
F_6;
g = x_(1,6)*(F_6)_21;
G = makeFreeOIModule(P, d, {5, 6});
S = makeSchreyerMonomialOrder(F, G, {f, g});
installSchreyerMonomialOrder S