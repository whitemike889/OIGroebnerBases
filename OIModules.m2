-- -*- coding: utf-8 -*-

-- PURPOSE: Algorithms for computing Gröbner bases, syzygies and free resolutions for submodules of free OI-modules over Noetherian polynomial OI-algebras
-- PROGRAMMER: Michael Morrow
-- LAST UPDATED: May 2022
-- COMMENT: This package was made using Macaulay2-Package-Template, available here: https://github.com/morrowmh/Macaulay2-Package-Template

newPackage("OIModules",
    Headline => "Computation in OI-modules over Noetherian polynomial OI-algebras",
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
-- EXPORT AND PROTECT ----------------------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

export {
    ------------------------------------
    -- From OIMap.m2 -------------------
    ------------------------------------

    -- Types
    "OIMap",

    -- Methods
    "makeOIMap", "getOIMaps", "composeOIMaps",

    ------------------------------------
    -- From PolynomialOIAlgebra.m2 -----
    ------------------------------------
    
    -- Types
    "PolynomialOIAlgebra",

    -- Methods
    "makePolynomialOIAlgebra", "getAlgebraInWidth", "getInducedAlgebraMap", "getInducedAlgebraMaps",

    ------------------------------------
    -- From FreeOIModuleMap.m2 ---------
    ------------------------------------

    -- Types
    "FreeOIModuleMap",
    
    -- Methods
    "makeFreeOIModuleMap",

    ------------------------------------
    -- From Terms.m2 -------------------
    ------------------------------------

    -- Types
    "BasisIndex", "OITerm",

    -- Methods
    "makeBasisIndex", "makeOITerm", "makeBasisElement", "getOITermsFromVector", "leadOITerm", "getVectorFromOITerms",

    ------------------------------------
    -- From FreeOIModule.m2 ------------
    ------------------------------------

    -- Types
    "FreeOIModule", "VectorInWidth", "ModuleInWidth",

    -- Methods
    "makeFreeOIModule", "installSchreyerMonomialOrder", "getFreeModuleInWidth", "freeOIModuleFromElement", "widthOfElement", "installBasisElement", "installBasisElements",

    -- Options
    "DegreeShifts",

    ------------------------------------
    -- From InducedModuleMap.m2 --------
    ------------------------------------

    -- Types
    "InducedModuleMap",

    -- Methods
    "getInducedModuleMap", "getInducedModuleMaps"
}

scan({
    ------------------------------------
    -- From OIMap.m2 -------------------
    ------------------------------------

    -- Keys
    Width, assignment,

    ------------------------------------
    -- From PolynomialOIAlgebra.m2 -----
    ------------------------------------

    -- Keys
    varRows, varSym, algebras, baseField, maps,

    ------------------------------------
    -- From FreeOIModuleMap.m2 ---------
    ------------------------------------

    -- Keys
    srcMod, targMod, genImage,

    ------------------------------------
    -- From Terms.m2 -------------------
    ------------------------------------

    -- Keys
    freeOIMod, idx, oiMap, ringElement, basisIndex,

    ------------------------------------
    -- From FreeOIModule.m2 ------------
    ------------------------------------

    -- Keys
    polyOIAlg, basisSym, genWidths, degShifts, monOrder, modules, basisElements

}, protect)

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- BODY ------------------------------------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- BEGIN: OIMap.m2 -------------------------------------------------------------
--------------------------------------------------------------------------------

-- PURPOSE: Define the new type OIMap
-- COMMENT: Should be of the form {Width => ZZ, assignment => List}
OIMap = new Type of HashTable
OIMap.synonym = "OI-map"

toString OIMap := f -> "width => "|toString f.Width|", assignment => "|toString f.assignment

net OIMap := f -> "Width: "|net f.Width || "Assignment: "|net f.assignment

source OIMap := f -> toList(1..#f.assignment)
target OIMap := f -> toList(1..f.Width)

-- PURPOSE: Make a new OIMap
-- INPUT: '(n, L)', a width 'n' and a list 'L'
-- OUTPUT: An OIMap made from n and L
makeOIMap = method(TypicalValue => OIMap)
makeOIMap(ZZ, List) := (n, L) -> new OIMap from {Width => n, assignment => L}

-- PURPOSE: Get all OI-maps between two widths
-- INPUT: '(m, n)', a width 'm' and a width 'n'
-- OUTPUT: A list of the OI-maps from m to n
getOIMaps = method(TypicalValue => List)
getOIMaps(ZZ, ZZ) := (m, n) -> (
    if n < m then return {};
    ret := new List;
    sets := subsets(set toList(1..n), m);
    for s in sets do ret = append(ret, new OIMap from {Width => n, assignment => sort toList s});
    ret
)

-- PURPOSE: Compose two OI-maps
-- INPUT: '(f, g)', an OIMap 'f' and an OIMap 'g'
-- OUTPUT: The OIMap f(g)
composeOIMaps = method(TypicalValue => OIMap)
composeOIMaps(OIMap, OIMap) := (f, g) -> (
    if not #f.assignment == g.Width then error "Maps cannot be composed due to incompatible source and target";
    L := new List;
    for i to #g.assignment - 1 do L = append(L, f.assignment#(g.assignment#i - 1));
    new OIMap from {Width => f.Width, assignment => L}
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
PolynomialOIAlgebra _ ZZ := (P, n) -> (
    alg := getAlgebraInWidth(P, n);
    use alg;
    alg
)

-- PURPOSE: Get the algebra map induced by an OI-map
-- INPUT: '(P, f)', a PolynomialOIAlgebra 'P' and an OIMap 'f'
-- OUTPUT: The map P(f)
getInducedAlgebraMap = method(TypicalValue => RingMap)
getInducedAlgebraMap(PolynomialOIAlgebra, OIMap) := (P, f) -> (
    -- Return the map if it already exists
    if P.maps#?(f.Width, f.assignment) then return P.maps#(f.Width, f.assignment);
    
    -- Generate the assignment
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

--------------------------------------------------------------------------------
-- BEGIN: FreeOIModule.m2 ------------------------------------------------------
--------------------------------------------------------------------------------

-- Define the new type FreeOIModule
-- COMMENT: Should be of the form {polyOIAlg => PolynomialOIAlgebra, basisSym => Symbol, genWidths => List, degShifts => List, monOrder => MutableList, modules => MutableHashTable, maps => MutableHashTable}
FreeOIModule = new Type of HashTable
FreeOIModule.synonym = "free OI-module"

toString FreeOIModule := F -> "generator widths => "|toString F.genWidths |", degree shifts => "|toString F.degShifts

net FreeOIModule := F -> (
    local monOrderNet;
    if F.monOrder#0 === Lex then monOrderNet = net Lex;
    if instance(F.monOrder#0, FreeOIModuleMap) then monOrderNet = "Schreyer monomial order via the FreeOIModuleMap: "|net F.monOrder#0;
    "Polynomial OI-algebra: "|toString F.polyOIAlg ||
    "Basis symbol: "|net F.basisSym ||
    "Generator widths: "|net F.genWidths ||
    "Degree shifts: "|net F.degShifts ||
    "Monomial order: "|monOrderNet
)

-- PURPOSE: Make a new FreeOIModule
-- INPUT: '(P, e, W)', a PolynomialOIAlgebra 'P', a Symbol 'e' and a List of generator widths 'W'
-- OUTPUT: A FreeOIModule made from P, e and W
-- COMMENT: Default monomial order is Lex
-- COMMENT: Default degree shifts are all zero
makeFreeOIModule = method(TypicalValue => FreeOIModule, Options => {DegreeShifts => null})
makeFreeOIModule(PolynomialOIAlgebra, Symbol, List) := opts -> (P, e, W) -> (
    if #W == 0 then error "Expected a non-empty list of generator widths";
    
    local shifts;
    if opts.DegreeShifts === null then shifts = #W : 0
    else if instance(opts.DegreeShifts, List) then shifts = opts.DegreeShifts
    else error("Invalid DegreeShifts option: "|toString opts.DegreeShifts);

    new FreeOIModule from {
        polyOIAlg => P,
        basisSym => e,
        genWidths => W,
        degShifts => toList shifts,
        monOrder => new MutableList from {Lex},
        modules => new MutableHashTable,
        maps => new MutableHashTable}
)

-- Define the new type ModuleInWidth
-- COMMENT: Should also contain the key-value pairs freeOIMod => FreeOIModule, Width => ZZ and basisElements => List
-- COMMENT: The order of basisElements matters, i.e. given a module M, basisElements#i should correspond to M_i
ModuleInWidth = new Type of Module
ModuleInWidth.synonym = "module in a specified width"

-- Define the new type VectorInWidth
-- COMMENT: An instance f should have class f === (corresponding ModuleInWidth)
VectorInWidth = new Type of Vector
VectorInWidth.synonym = "vector in a specified width"

--------------------------------------------------------------------------------
-- BEGIN: FreeOIModuleMap.m2 ---------------------------------------------------
--------------------------------------------------------------------------------

-- Define the new type FreeOIModuleMap
-- COMMENT: Should be of the form {srcMod => FreeOIModule, targMod => FreeOIModule, genImage => List}
-- COMMENT: genImage should be a list of the images of the generators of srcMod
-- COMMENT: The order of genImage matters, i.e. genImage#i should correspond to srcMod.genWidths#i
FreeOIModuleMap = new Type of HashTable
FreeOIModuleMap.synonym = "free OI-module map"

toString FreeOIModuleMap := f -> "source module => "|toString f.srcMod|", target module => "|toString f.targMod|", generator image => "|net f.genImage

net FreeOIModuleMap := f -> "Source module: "|toString f.srcMod ||
    "Target module: "|toString f.targMod ||
    "Generator image: "|net f.genImage

source FreeOIModuleMap := f -> f.srcMod
target FreeOIModuleMap := f -> f.targMod

-- PURPOSE: Make a new FreeOIModuleMap
-- INPUT: '(G, F, L)', a target FreeOIModule 'G', a source FreeOIModule 'F' and a List 'L' of elements of G
-- OUTPUT: A FreeOIModuleMap made from G, F and L
makeFreeOIModuleMap = method(TypicalValue => FreeOIModuleMap)
makeFreeOIModuleMap(FreeOIModule, FreeOIModule, List) := (G, F, L) -> new FreeOIModuleMap from {srcMod => F, targMod => G, genImage => L}

-- Install juxtaposition method for FreeOIModuleMap
FreeOIModuleMap List := (f, oiTerms) -> (
    if #oiTerms == 0 then error "Cannot apply FreeOIModuleMap to an empty list";

    -- Generate the new terms
    newTerms := new List;
    for oiTerm in oiTerms do (
        ringElement := oiTerm.ringElement;
        basisIndex := oiTerm.basisIndex;
        oiMap := basisIndex.oiMap;
        idx := basisIndex.idx;
        inducedModuleMap := getInducedModuleMap(f.targMod, oiMap);
        newTerms = append(newTerms, ringElement * inducedModuleMap(f.genImage#(idx - 1))) -- x*d_(pi,i) ---> x*F(pi)(b_i)
    );

    -- Sum the terms up
    ret := newTerms#0;
    for i from 1 to #newTerms - 1 do ret = ret + ret#i;
    ret
)

-- Vector version
FreeOIModuleMap VectorInWidth := (f, v) -> (
    freeOIMod := freeOIModuleFromElement v;
    if not source f === freeOIMod then error "Element "|net v|" does not belong to source of "|toString f;

    oiTerms := getOITermsFromVector v;
    f oiTerms
)

--------------------------------------------------------------------------------
-- END: FreeOIModuleMap.m2 -----------------------------------------------------
--------------------------------------------------------------------------------

-- PURPOSE: Install a Schreyer monomial order on a FreeOIModule
-- INPUT: A FreeOIModuleMap 'f'
-- OUTPUT: Sets f.srcMod.monOrder#0 to f
installSchreyerMonomialOrder = method()
installSchreyerMonomialOrder FreeOIModuleMap := f -> f.srcMod.monOrder#0 = f

net VectorInWidth := f -> (
    oiTerms := getOITermsFromVector f;
    if #oiTerms == 0 then return net 0;
    if #oiTerms == 1 then return net oiTerms#0;
    
    str := "";
    for i to #oiTerms - 2 do str = str|net oiTerms#i|" + ";
    str = str|net oiTerms#-1;
    str
)

--------------------------------------------------------------------------------
-- BEGIN: Terms.m2 -------------------------------------------------------------
--------------------------------------------------------------------------------

-- Define the new type BasisIndex
-- COMMENT: Should be of the form {freeOIMod => FreeOIModule, oiMap => OIMap, idx => ZZ}
BasisIndex = new Type of HashTable
BasisIndex.synonym = "basis index"

net BasisIndex := b -> net makeBasisElement b

-- PURPOSE: Make a new BasisIndex
-- INPUT: '(F, f, i)', a FreeOIModule 'F', an OIMap 'f' and an index 'i'
-- OUTPUT: A BasisIndex made from F, f and i
makeBasisIndex = method(TypicalValue => BasisIndex)
makeBasisIndex(FreeOIModule, OIMap, ZZ) := (F, f, i) -> new BasisIndex from {freeOIMod => F, oiMap => f, idx => i}

-- Define the new type OITerm
-- COMMENT: Should be of the form {ringElement => RingElement, basisIndex => BasisIndex}
OITerm = new Type of HashTable
OITerm.synonym = "OI-term"

-- PURPOSE: Make a new OITerm
-- INPUT: '(elt, b)', a RingElement 'elt' and a BasisIndex 'b'
-- OUTPUT: An OITerm made from elt and b
makeOITerm = method(TypicalValue => OITerm)
makeOITerm(RingElement, BasisIndex) := (elt, b) -> new OITerm from {ringElement => elt, basisIndex => b}

net OITerm := f -> (
    local ringElementNet;
    if #terms f.ringElement == 1 then ringElementNet = net f.ringElement
    else ringElementNet = "("|net f.ringElement|")";
    ringElementNet | net f.basisIndex.freeOIMod.basisSym_(toString f.basisIndex.oiMap.Width, toString f.basisIndex.oiMap.assignment, f.basisIndex.idx)
)

-- Comparison method for OITerm
OITerm ? OITerm := (f, g) -> (
    if f === g then return symbol ==;

    eltf := f.ringElement; eltg := g.ringElement;
    bf := f.basisIndex; bg := g.basisIndex;
    oiMapf := bf.oiMap; oiMapg := bg.oiMap;
    idxf := bf.idx; idxg := bg.idx;

    if not bf.freeOIMod === bg.freeOIMod then return incomparable;
    freeOIMod := bf.freeOIMod;

    monOrder := freeOIMod.monOrder#0;
    if monOrder === Lex then ( -- LEX ORDER
        if not idxf == idxg then if idxf < idxg then return symbol > else return symbol <;
        if not oiMapf.Width == oiMapg.Width then return oiMapf.Width ? oiMapg.Width;
        if not oiMapf.assignment == oiMapg.assignment then return oiMapf.assignment ? oiMapg.assignment;

        use class eltf; -- Note: since oiMapf.Width = oiMapg.Width we have class eltf = class eltg
        return eltf ? eltg
    )
    else if instance(monOrder, FreeOIModuleMap) then ( -- SCHREYER ORDER
        freeOIModuleMap := monOrder;
        imagef := freeOIModuleMap {f};
        imageg := freeOIModuleMap {g};
        if not leadOITerm imagef === leadOITerm imageg then return leadOITerm imagef ? leadOITerm imageg;
        if not idxf == idxg then if idxf < idxg then return symbol > else return symbol <;
        if not oiMapf.Width == oiMapg.Width then return oiMapf.Width ? oiMapg.Width;
        if not oiMapf.assignment == oiMapg.assignment then return oiMapf.assignment ? oiMapg.assignment;
        return symbol ==;
    )
    else error "Monomial order not supported"
)

-- PURPOSE: Make a basis element
-- INPUT: A BasisIndex 'b'
-- OUTPUT: An OITerm with ringElement = 1
makeBasisElement = method(TypicalValue => OITerm)
makeBasisElement BasisIndex := b -> (
    one := 1_(getAlgebraInWidth(b.freeOIMod.polyOIAlg, b.oiMap.Width));
    new OITerm from {ringElement => one, basisIndex => b}
)

-- PURPOSE: Convert an element from vector form to a list of OITerms
-- INPUT: A VectorInWidth 'f'
-- OUTPUT: A List of OITerms corresponding to the terms of f sorted from greatest to least
getOITermsFromVector = method(TypicalValue => List)
getOITermsFromVector VectorInWidth := f -> (
    freeOIMod := (class f).freeOIMod;
    Width := (class f).Width;
    freeMod := getFreeModuleInWidth(freeOIMod, Width);
    termList := new List;
    entryList := entries f;

    for i to #entryList - 1 do (
        if entryList#i == 0 then continue;

        basisElement := freeMod.basisElements#i;
        termList = append(termList, makeOITerm(entryList#i, basisElement.basisIndex))
    );

    reverse sort termList
)

-- PURPOSE: Convert an element from a list of OITerms to vector form
-- INPUT: A List 'L' of OITerms
-- OUTPUT: A VectorInWidth made from L
getVectorFromOITerms = method(TypicalValue => VectorInWidth)
getVectorFromOITerms List := L -> (
    if #L == 0 then return null;
    Width := (L#0).basisIndex.oiMap.Width;
    freeOIMod := (L#0).basisIndex.freeOIMod;
    freeMod := getFreeModuleInWidth(freeOIMod, Width);
    vect := 0_freeMod;

    for oiTerm in L do (
        ringElement := oiTerm.ringElement;
        basisElement := makeBasisElement oiTerm.basisIndex;
        pos := position(freeMod.basisElements, elt -> elt === basisElement);
        vect = vect + ringElement * freeMod_pos
    );
    
    vect
)

-- PURPOSE: Get the leading OITerm from a vector
-- INPUT: A VectorInWidth 'f'
-- OUTPUT: The largest OITerm in f
leadOITerm = method(TypicalValue => OITerm)
leadOITerm VectorInWidth := f -> (
    oiTerms := getOITermsFromVector f;
    if #oiTerms == 0 then return null;
    oiTerms#0
)

--------------------------------------------------------------------------------
-- END: Terms.m2 ---------------------------------------------------------------
--------------------------------------------------------------------------------

-- PURPOSE: Get the free module from a FreeOIModule in a specified width
-- INPUT: '(F, n)', a FreeOIModule 'F' and a width 'n'
-- OUTPUT: F_n, the width n free module of F
getFreeModuleInWidth = method(TypicalValue => ModuleInWidth)
getFreeModuleInWidth(FreeOIModule, ZZ) := (F, n) -> (
    -- Return the module if it already exists
    if F.modules#?n then return F.modules#n;

    -- Generate the degrees
    alg := getAlgebraInWidth(F.polyOIAlg, n);
    degList := new List;
    for i to #F.genWidths - 1 do degList = append(degList, binomial(n, F.genWidths#i) : F.degShifts#i);

    -- Make the module
    retHash := new MutableHashTable from alg^degList;
    retHash.Width = n;
    retHash.freeOIMod = F;
    retHash.basisElements = new List;
    
    -- Generate the basis elements
    for i to #F.genWidths - 1 do (
        oiMaps := getOIMaps(F.genWidths#i, n);
        for oiMap in oiMaps do retHash.basisElements = append(retHash.basisElements, makeBasisElement makeBasisIndex(F, oiMap, i + 1))
    );

    ret := new ModuleInWidth of VectorInWidth from retHash;

    -- Store the module
    F.modules#n = ret;

    ret
)

-- Subscript version of getFreeModuleInWidth
FreeOIModule _ ZZ := (F, n) -> (
    freeMod := getFreeModuleInWidth(F, n);
    use ring freeMod;
    freeMod
)

-- PURPOSE: Install a basis element for user input
-- OUTPUT: Sets the desired IndexedVariable to the appropriate basis vector
installBasisElement = method()

-- INPUT: '(F, n, f, i)', a FreeOIModule 'F', an integer 'n', a List 'f' and an index 'i'
installBasisElement(FreeOIModule, ZZ, List, ZZ) := (F, n, f, i) -> installBasisElement(F, makeOIMap(n, f), i)

-- INPUT: '(F, f, i)', a FreeOIModule 'F', an OIMap 'f' and an index 'i'
installBasisElement(FreeOIModule, OIMap, ZZ) := (F, f, i) -> (
    basisElement := makeBasisElement makeBasisIndex(F, f, i);
    installBasisElement basisElement
)

-- INPUT: An basis element OITerm 'b'
installBasisElement OITerm := b -> (
    freeOIMod := b.basisIndex.freeOIMod;
    Width := b.basisIndex.oiMap.Width;
    fmod := getFreeModuleInWidth(freeOIMod, Width);
    pos := position(fmod.basisElements, elt -> elt === b);

    if pos === null then error "Specified basis element does not exist";
    freeOIMod.basisSym_(Width, b.basisIndex.oiMap.assignment, b.basisIndex.idx) <- fmod_pos;
)

-- PURPOSE: Install all basis elements in a specified width
-- INPUT: '(F, n)', a FreeOIModule 'F' and a width 'n'
-- OUTPUT: Calls every installBasisElement() in F_n
-- COMMENT: This method is very slow for large n
installBasisElements = method()
installBasisElements(FreeOIModule, ZZ) := (F, n) ->
    for i to #F.genWidths - 1 do (
        oiMaps := getOIMaps(F.genWidths#i, n);
        for oiMap in oiMaps do installBasisElement(F, oiMap, i + 1)
    )

-- PURPOSE: Get the width of an element
-- INPUT: A Vector 'f'
-- OUTPUT: The width of f
widthOfElement = method(TypicalValue => ZZ)
widthOfElement VectorInWidth := f -> (class f).Width

-- PURPOSE: Get the FreeOIModule containing an element
-- INPUT: A Vector 'f'
-- OUTPUT: The FreeOIModule containing f
freeOIModuleFromElement = method(TypicalValue => FreeOIModule)
freeOIModuleFromElement VectorInWidth := f -> (class f).freeOIMod

--------------------------------------------------------------------------------
-- END: FreeOIModule.m2 --------------------------------------------------------
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- BEGIN: InducedModuleMap.m2 --------------------------------------------------
--------------------------------------------------------------------------------

-- Define the new type InducedModuleMap
-- COMMENT: Should be of the form {freeOIMod => FreeOIModule, oiMap => OIMap, assignment => HashTable}
-- COMMENT: assignment should specify how a BasisIndex in the source free module gets mapped to a basis index in the target free module
InducedModuleMap = new Type of HashTable
InducedModuleMap.synonym = "induced module map"

net InducedModuleMap := f -> "Source module: "|net source f ||
    "Target module: "|net target f ||
    "OI-map: "|toString f.oiMap ||
    "Assignment: "|net f.assignment

source InducedModuleMap := f -> getFreeModuleInWidth(f.freeOIMod, #f.oiMap.assignment)
target InducedModuleMap := f -> getFreeModuleInWidth(f.freeOIMod, f.oiMap.Width)

-- PURPOSE: Get the module map induced by an OI-map
-- INPUT: '(F, f)', a FreeOIModule 'F' and an OIMap 'f'
-- OUTPUT: The map F(f)
getInducedModuleMap = method(TypicalValue => InducedModuleMap)
getInducedModuleMap(FreeOIModule, OIMap) := (F, f) -> (
    -- Return the map if it already exists
    if F.maps#?(f.Width, f.assignment) then return F.maps#(f.Width, f.assignment);

    -- Generate the assignment
    m := #f.assignment;
    n := f.Width;
    fmodm := getFreeModuleInWidth(F, m);
    fmodn := getFreeModuleInWidth(F, n);
    basisElementsm := fmodm.basisElements;
    basisElementsn := fmodn.basisElements;
    mutableAssignment := new MutableHashTable;
    for basisElementm in basisElementsm do (
        newBasisIndex := makeBasisIndex(F, composeOIMaps(f, basisElementm.basisIndex.oiMap), basisElementm.basisIndex.idx);
        mutableAssignment#(basisElementm.basisIndex) = newBasisIndex
    );

    -- Make the map
    ret := new InducedModuleMap from {freeOIMod => F, oiMap => f, assignment => new HashTable from mutableAssignment};

    -- Store the map
    F.maps#(f.Width, f.assignment) = ret;

    ret
)

-- PURPOSE: Get the induced module maps between two widths
-- INPUT: '(F, m, n)', a FreeOIModule 'F', a width 'm' and a width 'n'
-- OUTPUT: A List of the elements in F(Hom(m,n))
getInducedModuleMaps = method(TypicalValue => List)
getInducedModuleMaps(FreeOIModule, ZZ, ZZ) := (F, m, n) -> (
    oiMaps := getOIMaps(m, n);
    ret := new List;
    for oiMap in oiMaps do ret = append(ret, getInducedModuleMap(F, oiMap));
    ret
)

-- Install juxtaposition method for InducedModuleMap
InducedModuleMap VectorInWidth := (f, v) -> (
    freeOIMod := f.freeOIMod;
    freeOIModFromVector := freeOIModuleFromElement v;
    if not freeOIMod === freeOIModFromVector then error "Incompatible free OI-modules";
    if not source f === class v then error "Element "|net v|" does not belong to source of "|toString f;

    algMap := getInducedAlgebraMap(freeOIMod.polyOIAlg, f.oiMap);
    newTerms := new List;
    for oiTerm in getOITermsFromVector v do (
        ringElement := oiTerm.ringElement;
        basisIndex := oiTerm.basisIndex;
        newRingElement := algMap ringElement;
        newBasisIndex := f.assignment#basisIndex;
        newTerms = append(newTerms, makeOITerm(newRingElement, newBasisIndex))
    );
    
    getVectorFromOITerms newTerms
)

--------------------------------------------------------------------------------
-- END: InducedModuleMap.m2 ----------------------------------------------------
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

restart
load "OIModules.m2"
P = makePolynomialOIAlgebra(QQ, 1, x);
F = makeFreeOIModule(P, e, {2,3});
installBasisElements(F, 5);
F_5;
f = x_(1,5)*e_(5, {2,3}, 1) + x_(1,3)^2*e_(5, {1,3,4}, 2);
installBasisElements(F, 6);
F_6;
g = x_(1,6)*e_(6, {1, 6}, 1) + x_(1,2)*e_(6, {2,4,6}, 2);
G = makeFreeOIModule(P, d, {5, 6});
phi = makeFreeOIModuleMap(F, G, {f, g});
installBasisElements(G, 7);
G_7;
h = x_(1,7)^2*x_(1,6)*d_(7, {1, 3, 4, 5, 7}, 1) + x_(1,5)^3*d_(7, {1, 4, 5, 6, 7}, 1);
installSchreyerMonomialOrder phi;
assert(leadOITerm h === (getOITermsFromVector(x_(1,5)^3*d_(7, {1, 4, 5, 6, 7}, 1)))#0)