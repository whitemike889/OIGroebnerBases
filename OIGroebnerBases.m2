-- -*- coding: utf-8 -*-

-- PURPOSE: Algorithms for computing Gröbner bases, syzygies and free resolutions for submodules of free OI-modules over Noetherian polynomial OI-algebras
-- PROGRAMMER: Michael Morrow
-- LAST UPDATED: July 2022
-- FIRST OFFICIAL RELEASE: 7/10/2022
-- COMMENT: This package was made using Macaulay2-Package-Template, available here: https://github.com/morrowmh/Macaulay2-Package-Template

newPackage("OIGroebnerBases",
    Headline => "Computation in OI-modules over Noetherian polynomial OI-algebras",
    Version => "1.0.4",
    Date => "April 4, 2022", -- Project birthday
    Keywords => { "Commutative Algebra" },
    Authors => {
        { Name => "Michael Morrow", HomePage => "https://michaelmorrow.org", Email => "michaelhmorrow98@gmail.com" }
    },
    DebuggingMode => false,
    HomePage => "https://github.com/morrowmh/OIGroebnerBases"
)

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- EXPORT AND PROTECT ----------------------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

export {
    -- Types
    "PolynomialOIAlgebra",
    "FreeOIModuleMap",
    "FreeOIModule",
    "OIResolution",

    -- Options
    "DegreeShifts", "MinimalOIGB",

    -- Methods
    "makePolynomialOIAlgebra", "getAlgebraInWidth",
    "makeFreeOIModuleMap",
    "makeFreeOIModule", "getDegShifts", "getGenWidths", "makeMonic", "getFreeModuleInWidth", "installBasisElements", "freeOIModuleFromElement",
    "oiGB", "isOIGB", "oiSyz",
    "oiRes", "isComplex"
}

scan({
    -- Keys
    Width, assignment,
    varRows, varSym, algebras, baseField, maps,
    srcMod, targMod, genImages,
    freeOIMod, idx, oiMap, ringElement, basisIndex, quo, rem, triples,
    polyOIAlg, basisSym, genWidths, degShifts, monOrder, modules, basisElements,

    -- Options
    Combine
}, protect)

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- BODY ------------------------------------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

-- Cache for storing OI-maps
oiMapCache = new MutableHashTable

-- PURPOSE: Define the new type OIMap
-- COMMENT: Should be of the form {Width => ZZ, assignment => List}
OIMap = new Type of HashTable

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
    
    -- Return the maps if they already exist
    if oiMapCache#?(m, n) then return oiMapCache#(m, n);

    ret := new MutableList;
    sets := subsets(toList(1..n), m);
    for i to #sets - 1 do ret#i = new OIMap from {Width => n, assignment => sets#i};
    ret = toList ret;

    -- Store the maps
    oiMapCache#(m, n) = ret;

    ret
)

-- PURPOSE: Compose two OI-maps
-- INPUT: '(f, g)', an OIMap 'f' and an OIMap 'g'
-- OUTPUT: The OIMap f(g)
composeOIMaps = method(TypicalValue => OIMap)
composeOIMaps(OIMap, OIMap) := (f, g) -> (
    if not #f.assignment == g.Width then error "Maps cannot be composed due to incompatible source and target";
    L := new MutableList;
    for i to #g.assignment - 1 do L#i = f.assignment#(g.assignment#i - 1);
    new OIMap from {Width => f.Width, assignment => toList L}
)

-- Define the new type PolynomialOIAlgebra
-- COMMENT: Should be of the form {baseField => Ring, varRows => ZZ, varSym => Symbol, algebras => MutableHashTable, maps => MutableHashTable}
PolynomialOIAlgebra = new Type of HashTable

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
linearFromRowCol(PolynomialOIAlgebra, ZZ, ZZ, ZZ) := (P, n, i, j) -> P.varRows * (n - j + 1) - i

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
    subs := new MutableList;
    k := 0;
    for j from 1 to m do
        for i from 1 to P.varRows do ( subs#k = src_(linearFromRowCol(P, m, i, j)) => targ_(linearFromRowCol(P, n, i, f.assignment#(j - 1))); k = k + 1 );
    
    -- Make the map
    ret := map(targ, src, toList subs);

    -- Store the map
    P.maps#(f.Width, f.assignment) = ret;

    ret
)

-- Define the new type FreeOIModule
-- COMMENT: Should be of the form {polyOIAlg => PolynomialOIAlgebra, basisSym => Symbol, genWidths => List, degShifts => List, monOrder => MutableList, modules => MutableHashTable, maps => MutableHashTable}
FreeOIModule = new Type of HashTable

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

-- PURPOSE: Get the generator widths of a FreeOIModule
-- INPUT: A FreeOIModule 'F'
-- OUTPUT: F.genWidths
getGenWidths = method(TypicalValue => List)
getGenWidths FreeOIModule := F -> F.genWidths

-- PURPOSE: Get the degree shifts of a FreeOIModule
-- INPUT: A FreeOIModule 'F'
-- OUTPUT: F.degShifts
getDegShifts = method(TypicalValue => List)
getDegShifts FreeOIModule := F -> F.degShifts

-- PURPOSE: Make a new FreeOIModule
-- INPUT: '(P, e, W)', a PolynomialOIAlgebra 'P', a Symbol 'e' and a List of generator widths 'W'
-- OUTPUT: A FreeOIModule made from P, e and W
-- COMMENT: Default monomial order is Lex
-- COMMENT: Default degree shifts are all zero
makeFreeOIModule = method(TypicalValue => FreeOIModule, Options => {DegreeShifts => null})
makeFreeOIModule(PolynomialOIAlgebra, Symbol, List) := opts -> (P, e, W) -> (
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

-- PURPOSE: Get the monomial order from a FreeOIModule
-- INPUT: A FreeOIModule 'F'
-- OUTPUT: The monomial order on F
-- COMMENT: Returns either Lex or a FreeOIModuleMap
getMonomialOrder = method()
getMonomialOrder FreeOIModule := F -> F.monOrder#0

-- Define the new type ModuleInWidth
-- COMMENT: Should also contain the key-value pairs freeOIMod => FreeOIModule, Width => ZZ and basisElements => List
-- COMMENT: The order of basisElements matters, i.e. given a module M, basisElements#i should correspond to M_i
ModuleInWidth = new Type of Module

net ModuleInWidth := M -> (
    rawMod := new Module from M;
    net rawMod | " in width " | net rawMod.Width
)

-- Define the new type VectorInWidth
-- COMMENT: An instance f should have class f === (corresponding ModuleInWidth)
VectorInWidth = new Type of Vector

-- PURPOSE: Check if a VectorInWidth is zero
-- INPUT: A VectorInWidth 'f'
-- OUTPUT: true if f is zero, false otherwise
isZero = method(TypicalValue => Boolean)
isZero VectorInWidth := f -> f == 0_(class f)

-- Define the new type FreeOIModuleMap
-- COMMENT: Should be of the form {srcMod => FreeOIModule, targMod => FreeOIModule, genImages => List}
-- COMMENT: genImages should be a list of the images of the generators of srcMod
-- COMMENT: The order of genImages matters, i.e. the width of genImages#i should equal srcMod.genWidths#i
-- COMMENT: To be a graded map, genImages should consist of homogeneous elements and degree(genImages#i) should equal -srcMod.degShifts#i
FreeOIModuleMap = new Type of HashTable

net FreeOIModuleMap := f -> "Source module: "|toString f.srcMod ||
    "Target module: "|toString f.targMod ||
    "Generator images: "|net f.genImages

source FreeOIModuleMap := f -> f.srcMod
target FreeOIModuleMap := f -> f.targMod

-- PURPOSE: Make a new FreeOIModuleMap
-- INPUT: '(G, F, L)', a target FreeOIModule 'G', a source FreeOIModule 'F' and a List 'L' of elements of G
-- OUTPUT: A FreeOIModuleMap made from G, F and L
makeFreeOIModuleMap = method(TypicalValue => FreeOIModuleMap)
makeFreeOIModuleMap(FreeOIModule, FreeOIModule, List) := (G, F, L) -> new FreeOIModuleMap from {srcMod => F, targMod => G, genImages => L}

-- PURPOSE: Check if a FreeOIModuleMap is zero
-- INPUT: A FreeOIModuleMap 'f'
-- OUTPUT: true if f is the zero map, false otherwise
isZero FreeOIModuleMap := f -> isZero f.srcMod or isZero f.targMod

-- PURPOSE: Apply a FreeOIModuleMap to a List of OITerms
-- INPUT: '(f, oiTerms)', a FreeOIModuleMap 'f' and a List of OITerms 'oiTerms'
-- OUTPUT: The VectorInWidth f(oiTerms)
fommToOITerms = method(TypicalValue => VectorInWidth)
fommToOITerms(FreeOIModuleMap, List) := (f, oiTerms) -> (
    if #oiTerms == 0 then error "Cannot apply FreeOIModuleMap to an empty list";

    -- Handle the zero map case
    if isZero f then (
        Width := (oiTerms#0).basisIndex.oiMap.Width;
        return 0_(getFreeModuleInWidth(f.targMod, Width))
    );

    -- Generate the new terms
    newTerms := new MutableList;
    for i to #oiTerms - 1 do (
        ringElement := (oiTerms#i).ringElement;
        basisIndex := (oiTerms#i).basisIndex;
        oiMap := basisIndex.oiMap;
        idx := basisIndex.idx;
        inducedModuleMap := getInducedModuleMap(f.targMod, oiMap);
        newTerms#i = ringElement * inducedModuleMap(f.genImages#(idx - 1)) -- x*d_(pi,i) ---> x*F(pi)(b_i)
    );

    -- Sum the terms up
    sum toList newTerms
)

-- Install juxtaposition method for FreeOIModuleMap and List
-- COMMENT: Applies a FreeOIModuleMap to a List of VectorInWidths
FreeOIModuleMap List := (f, L) -> for i to #L - 1 list f L#i

-- Install juxtaposition method for FreeOIModuleMap and List
-- COMMENT: Applies a FreeOIModuleMap to the List of OITerms obtained from a VectorInWidth
FreeOIModuleMap VectorInWidth := (f, v) -> (
    freeOIMod := freeOIModuleFromElement v;
    if not source f === freeOIMod then error "Element "|net v|" does not belong to source of "|toString f;

    -- Handle the zero map and zero vector cases
    if isZero f or isZero v then (
        Width := widthOfElement v;
        return 0_(getFreeModuleInWidth(f.targMod, Width))
    );

    oiTerms := getOITermsFromVector v;
    fommToOITerms(f, oiTerms)
)

-- Check if a FreeOIModuleMap is a graded map
isHomogeneous FreeOIModuleMap := f -> (
    if isZero f then return true;

    for elt in f.genImages do (
        degs := for t in terms elt list degree t;
        if not #(set degs) == 1 then return false
    );

    -f.srcMod.degShifts == flatten apply(f.genImages, degree)
)

-- PURPOSE: Install a Schreyer monomial order on a FreeOIModule
-- INPUT: A FreeOIModuleMap 'f'
-- OUTPUT: Sets f.srcMod.monOrder#0 to f
installSchreyerMonomialOrder = method()
installSchreyerMonomialOrder FreeOIModuleMap := f -> f.srcMod.monOrder#0 = f

net VectorInWidth := f -> (
    if isZero f then return net 0;
    oiTerms := getOITermsFromVector(f, Combine => true);
    if #oiTerms == 0 then return net 0;
    if #oiTerms == 1 then return net oiTerms#0;
    
    str := "";
    for i to #oiTerms - 2 do str = str|net oiTerms#i|" + ";
    str = str|net oiTerms#-1;
    str
)

-- Comparison method for VectorInWidth
-- COMMENT: Compares vectors by looking at their lead terms
VectorInWidth ? VectorInWidth := (f, g) -> leadOITerm f ? leadOITerm g

-- PURPOSE: Make a List of VectorInWidths monic
-- INPUT: A List 'L'
-- OUTPUT: A List containing f // leadCoefficient f for all f in L
makeMonic = method(TypicalValue => List)
makeMonic List := L -> (
    ret := new MutableList;

    for i to #L - 1 do (
        f := L#i;
        if isZero f then (ret#i = f; continue);
        oiterms := getOITermsFromVector f;
        lotf := leadOITerm f;
        lcf := leadCoefficient lotf.ringElement;
        newTerms := for oiterm in oiterms list makeOITerm(oiterm.ringElement // lcf, oiterm.basisIndex);
        ret#i = getVectorFromOITerms newTerms
    );

    new List from ret
)

-- Define the new type BasisIndex
-- COMMENT: Should be of the form {freeOIMod => FreeOIModule, oiMap => OIMap, idx => ZZ}
BasisIndex = new Type of HashTable

-- PURPOSE: Make a new BasisIndex
-- INPUT: '(F, f, i)', a FreeOIModule 'F', an OIMap 'f' and an index 'i'
-- OUTPUT: A BasisIndex made from F, f and i
-- COMMENT: i should start at 1
makeBasisIndex = method(TypicalValue => BasisIndex)
makeBasisIndex(FreeOIModule, OIMap, ZZ) := (F, f, i) -> new BasisIndex from {freeOIMod => F, oiMap => f, idx => i}

-- Define the new type OITerm
-- COMMENT: Should be of the form {ringElement => RingElement, basisIndex => BasisIndex}
OITerm = new Type of HashTable

-- PURPOSE: Make a new OITerm
-- INPUT: '(elt, b)', a RingElement 'elt' and a BasisIndex 'b'
-- OUTPUT: An OITerm made from elt and b
makeOITerm = method(TypicalValue => OITerm)
makeOITerm(RingElement, BasisIndex) := (elt, b) -> new OITerm from {ringElement => elt, basisIndex => b}

net OITerm := f -> (
    local ringElementNet;
    if #terms f.ringElement == 1 or #terms f.ringElement == 0 then ringElementNet = net f.ringElement
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

    monOrder := getMonomialOrder freeOIMod;
    if monOrder === Lex then ( -- LEX ORDER
        if not idxf == idxg then if idxf < idxg then return symbol > else return symbol <;
        if not oiMapf.Width == oiMapg.Width then return oiMapf.Width ? oiMapg.Width;
        if not oiMapf.assignment == oiMapg.assignment then return oiMapf.assignment ? oiMapg.assignment;

        use class eltf; -- Note: since oiMapf.Width = oiMapg.Width we have class eltf = class eltg
        return eltf ? eltg
    )
    else if instance(monOrder, FreeOIModuleMap) then ( -- SCHREYER ORDER
        freeOIModuleMap := monOrder;
        imagef := fommToOITerms(freeOIModuleMap, {f});
        imageg := fommToOITerms(freeOIModuleMap, {g});
        lotimf := leadOITerm imagef;
        lotimg := leadOITerm imageg;
        lomimf := makeOITerm(lotimf.ringElement // leadCoefficient lotimf.ringElement, lotimf.basisIndex);
        lomimg := makeOITerm(lotimg.ringElement // leadCoefficient lotimg.ringElement, lotimg.basisIndex);

        if not lomimf === lomimg then return lomimf ? lomimg;
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
-- COMMENT: "Combine => true" will combine like terms
getOITermsFromVector = method(TypicalValue => List, Options => {Combine => false})
getOITermsFromVector VectorInWidth := opts -> f -> (
    if isZero f then return {};
    freeOIMod := (class f).freeOIMod;
    Width := (class f).Width;
    freeMod := getFreeModuleInWidth(freeOIMod, Width);
    termList := new MutableList;
    entryList := entries f;

    k := 0;
    for i to #entryList - 1 do (
        if entryList#i == 0 then continue;

        basisElement := freeMod.basisElements#i;
        if opts.Combine then (
            termList#k = makeOITerm(entryList#i, basisElement.basisIndex);
            k = k + 1
        ) else (
            termsInEntry := terms entryList#i;
            for term in termsInEntry do ( termList#k = makeOITerm(term, basisElement.basisIndex); k = k + 1 )
        )
    );

    reverse sort toList termList
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

-- PURPOSE: Divide one OI-term by another
oiTermDiv = method(TypicalValue => HashTable)

-- INPUT: '(f, g)', an OITerm 'f' and an OITerm 'g'
-- OUTPUT: A HashTable of the form {quo => RingElement, oiMap => OIMap}
-- COMMENT: Returns {quo => 0, oiMap => null} if division does not occur
oiTermDiv(OITerm, OITerm) := (f, g) -> (
    freeOIModf := f.basisIndex.freeOIMod;
    freeOIModg := g.basisIndex.freeOIMod;

    retZero := new HashTable from {quo => 0_(class f.ringElement), oiMap => null};
    if not freeOIModf === freeOIModg then return retZero;

    Widthf := f.basisIndex.oiMap.Width;
    Widthg := g.basisIndex.oiMap.Width;
    if Widthf < Widthg then return retZero;
    if Widthf == Widthg then (
        if not f.basisIndex === g.basisIndex then return retZero;
        if f.ringElement % g.ringElement == 0 then return new HashTable from {quo => f.ringElement // g.ringElement, oiMap => (getOIMaps(Widthg, Widthf))#0} else return retZero
    );

    oiMaps := getOIMaps(Widthg, Widthf);
    for oimap in oiMaps do (
        moduleMap := getInducedModuleMap(freeOIModf, oimap);
        imageg := leadOITerm moduleMap {g};
        if not imageg.basisIndex === f.basisIndex then continue;
        if f.ringElement % imageg.ringElement == 0 then return new HashTable from {quo => f.ringElement // imageg.ringElement, oiMap => oimap} else continue
    );

    retZero
)

-- INPUT: '(f, g)', a VectorInWidth 'f' and a VectorInWidth 'g'
-- OUTPUT: Performs oiTermDiv on lt(f) and lt(g)
oiTermDiv(VectorInWidth, VectorInWidth) := (f, g) -> oiTermDiv(leadOITerm f, leadOITerm g)

-- PURPOSE: Get the least common multiple of two OITerms
-- INPUT: '(f, g)', an OITerm 'f' and an OITerm 'g'
-- OUTPUT: The LCM of f and g
lcm(OITerm, OITerm) := (f, g) -> (
    if not f.basisIndex === g.basisIndex then return makeOITerm(0_(class f.ringElement), f.basisIndex);

    makeOITerm(lcm(f.ringElement // leadCoefficient f.ringElement, g.ringElement // leadCoefficient g.ringElement), f.basisIndex)
)

-- PURPOSE: Get the least common multiple of the lead OI-term of two VectorInWidths
-- INPUT: '(f, g)', a VectorInWidth 'f' and a VectorInWidth 'g'
-- OUTPUT: The LCM of lt(f) and lt(g)
lcm(VectorInWidth, VectorInWidth) := (f, g) -> lcm(leadOITerm f, leadOITerm g)

-- Check if an OITerm is zero
isZero OITerm := f -> f.ringElement == 0_(class f.ringElement)

-- Check if a RingElement is zero
isZero RingElement := f -> f == 0_(class f)

-- Get the terms in a VectorInWidth
terms VectorInWidth := f -> (
    oiTerms := getOITermsFromVector f;
    for oiTerm in oiTerms list getVectorFromOITerms {oiTerm}
)

-- PURPOSE: Check if a FreeOIModule is zero
-- INPUT: A FreeOIModule 'F'
-- OUTPUT: true if #F.genWidths = 0, false otherwise
isZero FreeOIModule := F -> #F.genWidths == 0

-- PURPOSE: Get the free module from a FreeOIModule in a specified width
-- INPUT: '(F, n)', a FreeOIModule 'F' and a width 'n'
-- OUTPUT: F_n, the width n free module of F
getFreeModuleInWidth = method(TypicalValue => ModuleInWidth)
getFreeModuleInWidth(FreeOIModule, ZZ) := (F, n) -> (
    -- Return the module if it already exists
    if F.modules#?n then return F.modules#n;

    -- Generate the degrees
    alg := getAlgebraInWidth(F.polyOIAlg, n);
    degList := new MutableList;
    for i to #F.genWidths - 1 do degList#i = binomial(n, F.genWidths#i) : F.degShifts#i;

    -- Make the module
    retHash := new MutableHashTable from alg^(toList degList);
    retHash.Width = n;
    retHash.freeOIMod = F;
    
    -- Generate the basis elements
    k := 0;
    mutableBasisElements := new MutableList;
    for i to #F.genWidths - 1 do (
        oiMaps := getOIMaps(F.genWidths#i, n);
        for oiMap in oiMaps do ( mutableBasisElements#k = makeBasisElement makeBasisIndex(F, oiMap, i + 1); k = k + 1 )
    );
    retHash.basisElements = toList mutableBasisElements;

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

freeOIModuleFromElement Vector := f -> (
    if not (class f).?freeOIMod then error "Element does not belong to a FreeOIModule";
    freeOIModuleFromElement f
)

-- Define the new type InducedModuleMap
-- COMMENT: Should be of the form {freeOIMod => FreeOIModule, oiMap => OIMap, assignment => HashTable}
-- COMMENT: assignment should specify how a BasisIndex in the source free module gets mapped to a basis index in the target free module
InducedModuleMap = new Type of HashTable

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

-- Install juxtaposition method for InducedModuleMap and List
-- COMMENT: Applies an InducedModuleMap to a List of OITerms and returns the resulting VectorInWidth
InducedModuleMap List := (f, oiTerms) -> (
    if #oiTerms == 0 then error "Cannot apply InducedModuleMap to an empty list";

    -- Generate the new terms
    algMap := getInducedAlgebraMap(f.freeOIMod.polyOIAlg, f.oiMap);
    newTerms := new MutableList;
    for i to #oiTerms - 1 do (
        ringElement := (oiTerms#i).ringElement;
        basisIndex := (oiTerms#i).basisIndex;
        newRingElement := algMap ringElement;
        newBasisIndex := f.assignment#basisIndex;
        newTerms#i = makeOITerm(newRingElement, newBasisIndex)
    );
    
    getVectorFromOITerms toList newTerms
)

-- Install juxtaposition method for InducedModuleMap and VectorInWidth
InducedModuleMap VectorInWidth := (f, v) -> (
    freeOIMod := f.freeOIMod;
    freeOIModFromVector := freeOIModuleFromElement v;
    if not freeOIMod === freeOIModFromVector then error "Incompatible free OI-modules";
    if not source f === class v then error "Element "|net v|" does not belong to source of "|toString f;

    -- Handle the zero vector
    if isZero v then (
        targWidth := f.oiMap.Width;
        return 0_(getFreeModuleInWidth(freeOIMod, targWidth))
    );

    f getOITermsFromVector v
)

-- PURPOSE: Compute a remainder of a VectorInWidth modulo a List of VectorInWidths
-- INPUT: '(f, L)', a VectorInWidth 'f' and a List 'L'
-- OUTPUT: A HashTable of the form {quo => VectorInWidth, rem => VectorInWidth, triples => List} where triples is a List describing how the quotient is constructed
-- COMMENT: If the elements of L are {l0, l1, l2} then triples may look like {{ringElt1, oiMap1, 0}, {ringElt2, oiMap2, 2}} and quo = ringElt1*F(oiMap1)(l0)+ringElt2*F(oiMap2)(l2)
-- COMMENT: "Verbose => true" will print more information
oiPolyDiv = method(TypicalValue => HashTable, Options => {Verbose => false})
oiPolyDiv(VectorInWidth, List) := opts -> (f, L) -> (
    if #L == 0 then error "Expected nonempty List";

    if opts.Verbose then print("Dividing "|net f|" by "|net L);

    if isZero f then return new HashTable from {quo => f, rem => f, triples => {}};

    local retTmp;
    retTmp = new MutableHashTable from {quo => 0_(class f), rem => f, triples => new MutableList};
    tripIndex := 0;
    while true do (
        divisionOccurred := false;
        for elt in L do (
            div := oiTermDiv(retTmp.rem, elt);
            if isZero div.quo then continue;

            moduleMap := getInducedModuleMap(freeOIModuleFromElement f, div.oiMap);
            q := moduleMap elt;
            retTmp.quo = retTmp.quo + div.quo * q;
            retTmp.triples#tripIndex = {div.quo, div.oiMap, position(L, l -> l === elt)};
            tripIndex = tripIndex + 1;

            retTmp.rem = retTmp.rem - div.quo * q;

            if isZero retTmp.rem then return new HashTable from {rem => retTmp.rem, quo => retTmp.quo, triples => new List from retTmp.triples};
            divisionOccurred = true;
            break
        );

        if not divisionOccurred then break
    );

    retTmp
)

-- PURPOSE: Compute the S-polynomial of two VectorInWidths
-- INPUT: '(f, g)', a VectorInWidth 'f' and a VectorInWidth 'g'
-- OUTPUT: The S-polynomial S(f, g)
-- COMMENT: Returns zero if either f or g is zero or if lcm(leadOITerm f, leadOITerm g) is zero
spoly = method(TypicalValue => VectorInWidth)
spoly(VectorInWidth, VectorInWidth) := (f, g) -> (
    Widthf := widthOfElement f;
    Widthg := widthOfElement g;
    if not Widthf == Widthg then error "Vectors must belong to the same width";

    freeOIModf := freeOIModuleFromElement f;
    freeOIModg := freeOIModuleFromElement g;
    if not freeOIModf === freeOIModg then error "Vectors must belong to the same free OI-module";
    freeMod := getFreeModuleInWidth(freeOIModf, Widthf);

    if isZero f or isZero g then return 0_freeMod;

    lotf := leadOITerm f;
    lotg := leadOITerm g;
    lcmfg := lcm(lotf, lotg);
    if isZero lcmfg then return 0_freeMod;
    (lcmfg.ringElement // lotf.ringElement)*f - (lcmfg.ringElement // lotg.ringElement)*g
)

-- PURPOSE: Generate a List of OI-pairs from a List of VectorInWidths
-- INPUT: A List 'L'
-- OUTPUT: A List of Lists of the form {VectorInWidth, VectorInWidth, OIMap, OIMap, ZZ, ZZ}
-- COMMENT: The first two VectorInWidths are the actual OI-pair. Then the OI-maps used to make them, and the indices of the elements of L used
-- COMMENT: "Verbose => true" will print more information
oiPairs = method(TypicalValue => List, Options => {Verbose => false})
oiPairs List := opts -> L -> (
    if #L == 0 then error "Expected a nonempty List";

    ret := new MutableList;
    l := 0;
    for fIdx to #L - 1 do (
        f := L#fIdx;
        lotf := leadOITerm f;
        Widthf := widthOfElement f;
        for gIdx from fIdx to #L - 1 do (
            g := L#gIdx;
            Widthg := widthOfElement g;
            lotg := leadOITerm g;
            if not lotf.basisIndex.idx == lotg.basisIndex.idx then continue; -- These will have lcm zero

            if opts.Verbose then print("Generating pairs for "|net f|" and "|net g);

            searchMin := max(Widthf, Widthg);
            searchMax := Widthf + Widthg;
            for i to searchMax - searchMin do (
                k := searchMax - i;
                oiMapsFromf := getOIMaps(Widthf, k);

                -- Given an OI-map out of f, we construct the corresponding OI-maps out of g
                for oiMapFromf in oiMapsFromf do (
                    base := set(1..k) - set oiMapFromf.assignment; -- Get the starting set

                    -- Now add back in the i-element subsets of oiMapFromf.assignment and make the pairs
                    for subset in subsets(oiMapFromf.assignment, i) do (
                        oiMapFromg := makeOIMap(k, sort toList(base + set subset));
                        if not composeOIMaps(oiMapFromf, lotf.basisIndex.oiMap) === composeOIMaps(oiMapFromg, lotg.basisIndex.oiMap) then continue; -- These will have lcm zero

                        if opts.Verbose then print("Found OI-maps "|net oiMapFromf|" and "|net oiMapFromg);

                        moduleMapFromf := getInducedModuleMap(freeOIModuleFromElement f, oiMapFromf);
                        moduleMapFromg := getInducedModuleMap(freeOIModuleFromElement g, oiMapFromg);

                        candidate := {moduleMapFromf f, moduleMapFromg g, oiMapFromf, oiMapFromg, fIdx, gIdx};
                        if not member(candidate, toList ret) then (ret#l = candidate; l = l + 1) -- Avoid duplicates
                    )
                )
            )
        )
    );

    toList ret
)

-- Cache for storing OI-Groebner bases
oiGBCache = new MutableHashTable

-- PURPOSE: Compute a Groebner basis
-- INPUT: A List 'L' of VectorInWidths
-- OUTPUT: A Groebner basis made from L
-- COMMENT: Uses the OI-Buchberger's Algorithm
-- COMMENT: "Verbose => true" will print more information
-- COMMENT: "Strategy => 1" recalculates the OI-pairs every time a nonzero remainder is found
-- COMMENT: "Strategy => 2" adds all nonzero remainders before recalculating the OI-pairs
-- COMMENT: "MinimalOIGB => false" will not minimize the basis at the end
oiGB = method(TypicalValue => List, Options => {Verbose => false, Strategy => 1, MinimalOIGB => true})
oiGB List := opts -> L -> (

    if not (opts.Strategy == 1 or opts.Strategy == 2) then error "Expected Strategy => 1 or Strategy => 2";

    -- Return the GB if it already exists
    if oiGBCache#?(L, opts.Strategy, opts.MinimalOIGB) then return oiGBCache#(L, opts.Strategy, opts.MinimalOIGB);

    if #L == 0 then error "Expected a nonempty List";
    if #L == 1 then if isZero L#0 then return false else return L;
    
    ret := new MutableList from L;
    encountered := new MutableList;
    addedTotal := 0;
    encIndex := 0;
    retIndex := #ret;
    
    -- Enter the main loop: terminates by an equivariant Noetherianity argument
    while true do (
        retTmp := toList ret;
        addedThisPhase := 0;

        oipairs := oiPairs(retTmp, Verbose => opts.Verbose);
        for i to #oipairs - 1 do (
            s := spoly(oipairs#i#0, oipairs#i#1);

            if isZero s or member(s, toList encountered) then continue; -- Skip zero and redundant S-polynomials
            encountered#encIndex = s;
            encIndex = encIndex + 1;

            if opts.Verbose then (
                print("On pair "|toString(i + 1)|" out of "|toString(#oipairs));
                if opts.Strategy == 2 then print("Elements added so far this phase: "|toString addedThisPhase);
                print("Elements added total: "|toString addedTotal)
            );

            rem := (oiPolyDiv(s, toList ret, Verbose => opts.Verbose)).rem;
            if not isZero rem and not member(rem, toList ret) then (
                if opts.Verbose then print("Nonzero remainder: "|net rem);
                ret#retIndex = rem;
                retIndex = retIndex + 1;

                addedThisPhase = addedThisPhase + 1;
                addedTotal = addedTotal + 1;

                if opts.Strategy == 1 then break
            )
        );

        if toList ret === retTmp then break -- No new elements were added so we're done by the OI-Buchberger's Criterion
    );

    -- Minimize the basis
    local finalRet;
    if opts.MinimalOIGB then finalRet = minimizeOIGB(toList ret, Verbose => opts.Verbose) else finalRet = toList ret;

    -- Store the basis
    oiGBCache#(L, opts.Strategy, opts.MinimalOIGB) = finalRet;

    finalRet
)

-- PURPOSE: Minimize an OI-Groebner basis
-- INPUT: A List 'L'
-- OUTPUT: Assuming L is an OI-Groebner basis, returns a minimized basis made from L
-- COMMENT: "Minimal" in the sense of lt(p) not in <lt(L - {p})> for all p in L
-- COMMENT: "Verbose => true" will print more information
minimizeOIGB = method(TypicalValue => List, Options => {Verbose => false})
minimizeOIGB List := opts -> L -> (
    if opts.Verbose then print "Computing minimal OIGB...";

    currentBasis := L;
    while true do (
        redundantFound := false;

        for p in currentBasis do (
            minusp := toList((set currentBasis) - set {p});
            for elt in minusp do if not isZero (oiTermDiv(p, elt)).quo then (
                if opts.Verbose then print("Found redundant element: "|net p);
                redundantFound = true;
                currentBasis = minusp;
                break
            );

            if redundantFound then break
        );

        if not redundantFound then break
    );

    currentBasis
)

-- PURPOSE: Check if a List is an OI-Groebner basis
-- INPUT: A List 'L' of VectorInWidths
-- OUTPUT: true if L is an OI-Groebner basis, false otherwise
-- COMMENT: "Verbose => true" will print more information
isOIGB = method(TypicalValue => Boolean, Options => {Verbose => false})
isOIGB List := opts -> L -> (
    if #L == 0 then return false;
    if #L == 1 then if isZero L#0 then return false else return true;

    encountered := new MutableList;
    encIndex := 0;
    oipairs := oiPairs(L, Verbose => opts.Verbose);
    for i to #oipairs - 1 do (
        if opts.Verbose then (
            print("On pair "|toString(i + 1)|" out of "|toString(#oipairs));
            print("Pair: "|net oipairs#i)
        );

        s := spoly(oipairs#i#0, oipairs#i#1);
        if isZero s or member(s, toList encountered) then continue;

        encountered#encIndex = s;
        encIndex = encIndex + 1;
        rem := (oiPolyDiv(s, L, Verbose => opts.Verbose)).rem;
        if not isZero rem then (if opts.Verbose then print("Nonzero remainder: "|net rem); return false) -- If L were a GB, then every element would have a unique remainder of zero
    );
    
    true
)

-- Cache for storing Groebner bases computed with oiSyz
oiSyzCache = new MutableHashTable

-- PURPOSE: Compute an OI-Groebner basis for the syzygy module of a List of VectorInWidths
-- INPUT: '(L, d)', a List 'L' of VectorInWidths and a basis Symbol 'd'
-- OUTPUT: Assuming L is an OI-Groebner basis, outputs an OI-Groebner basis for the syzygy module of L
-- COMMENT: Uses the OI-Schreyer's Theorem
oiSyz = method(TypicalValue => List, Options => {Verbose => false, MinimalOIGB => true})
oiSyz(List, Symbol) := opts -> (L, d) -> (
    if #L == 0 then error "Expected a nonempty list";
    
    -- Return the GB if it already exists
    if oiSyzCache#?(L, d, opts.MinimalOIGB) then return oiSyzCache#(L, d, opts.MinimalOIGB);
    
    freeOIMod := freeOIModuleFromElement L#0;
    shifts := for elt in L list -degree elt;
    widths := for elt in L list widthOfElement elt;
    G := makeFreeOIModule(freeOIMod.polyOIAlg, d, widths, DegreeShifts => flatten shifts);
    S := makeFreeOIModuleMap(freeOIMod, G, L);
    installSchreyerMonomialOrder S;

    ret := new MutableList;
    retIndex := 0;
    oipairs := oiPairs(L, Verbose => opts.Verbose);
    if opts.Verbose then print "Iterating through pairs...";
    i := 0;
    for pair in oipairs do (
        lotf := leadOITerm pair#0;
        lotg := leadOITerm pair#1;
        lcmfg := lcm(lotf, lotg);
        if isZero lcmfg then continue; -- This will yield a trivial syzygy

        if opts.Verbose then (print("On pair "|toString(i + 1)|" out of "|toString(#oipairs)); i = i + 1);
        if opts.Verbose then print("Pair: "|net pair);

        s := spoly(pair#0, pair#1);
        swidth := widthOfElement s;
        freeMod := getFreeModuleInWidth(G, swidth);
        thingToSubtract := 0_freeMod;
        if not isZero s then (
            sdiv := oiPolyDiv(s, L, Verbose => opts.Verbose);

            -- Calculate the stuff to subtract off
            for triple in sdiv.triples do (
                b := makeBasisElement makeBasisIndex(G, triple#1, 1 + triple#2);
                thingToSubtract = thingToSubtract + triple#0 * getVectorFromOITerms {b}
            )
        );

        bSigma := makeBasisElement makeBasisIndex(G, pair#2, 1 + pair#4);
        bTau := makeBasisElement makeBasisIndex(G, pair#3, 1 + pair#5);

        -- Make the syzygy
        syzygy := (lcmfg.ringElement // lotf.ringElement) * getVectorFromOITerms {bSigma} - (lcmfg.ringElement // lotg.ringElement) * getVectorFromOITerms {bTau} - thingToSubtract;
        
        if isZero syzygy then continue; -- Skip trivial syzygies

        ret#retIndex = syzygy;
        if opts.Verbose then print("Generated syzygy "|net ret#retIndex);
        retIndex = retIndex + 1
    );

    -- Minimize the basis
    local finalRet;
    if opts.MinimalOIGB then finalRet = minimizeOIGB(toList ret, Verbose => opts.Verbose) else finalRet = toList ret; 

    -- Store the GB
    oiSyzCache#(L, d, opts.MinimalOIGB) = finalRet;

    finalRet
)

-- Cache for storing OI-resolutions computed with oiRes
oiResCache = new MutableHashTable

-- Define the new Type OIResolution
-- COMMENT: Should be of the form {dd => List, modules => List}
OIResolution = new Type of HashTable

net OIResolution := C -> (
    n := "0: "|toString C.modules#0;
    for i from 1 to #C.modules - 1 do n = n || toString i | ": "|toString C.modules#i;
    n
)

describe OIResolution := C -> (
    n := "0: Module: "|net C.modules#0||"Differential: "|net C.dd#0;
    for i from 1 to #C.modules - 1 do n = n || toString i | ": Module: "|net C.modules#i||"Differential: "|net C.dd#i;
    n
)

OIResolution _ ZZ := (C, n) -> C.modules#n

-- PURPOSE: Make an OI-resolution from an OI-Groebner basis
-- INPUT: '(L, n)', a List 'L' and an integer 'n'
-- OUTPUT: An OIResolution of length n for the OI-module generated by the elements of L
-- COMMENT: "FastNonminimal => true" will not minimize the resolution (in the graded case)
-- COMMENT: "Verbose => true" will print more information
-- COMMENT: "MinimalOIGB => false" will not compute a minimal GB at each step
oiRes = method(TypicalValue => OIResolution, Options => {FastNonminimal => false, Verbose => false, MinimalOIGB => true})
oiRes(List, ZZ) := opts -> (L, n) -> (
    if n < 0 then error "Expected nonnegative integer";
    if #L == 0 then error "Expected nonempty List";

    -- Return the resolution if it already exists
    if oiResCache#?(L, n, opts.FastNonminimal, opts.MinimalOIGB) then return oiResCache#(L, n, opts.FastNonminimal, opts.MinimalOIGB);

    ddMut := new MutableList;
    modulesMut := new MutableList;

    -- Make the initial resolution
    freeOIMod := freeOIModuleFromElement L#0;
    e := freeOIMod.basisSym;

    if opts.Verbose then print "Computing an OI-Groebner basis...";
    oigb := oiGB(L, Verbose => opts.Verbose, MinimalOIGB => opts.MinimalOIGB);

    if opts.Verbose then print "----------------------------------------\n----------------------------------------\nComputing syzygies...";
    currentGB := oigb;
    for i to n do (
        currentSymbol := getSymbol concatenate(e, toString i);
        syzGens := oiSyz(currentGB, currentSymbol, Verbose => opts.Verbose, MinimalOIGB => opts.MinimalOIGB);
        if #syzGens == 0 then (
            shifts := for elt in currentGB list -degree elt;
            widths := for elt in currentGB list widthOfElement elt;
            modulesMut#i = makeFreeOIModule(freeOIMod.polyOIAlg, currentSymbol, widths, DegreeShifts => flatten shifts);
            ddMut#i = makeFreeOIModuleMap(freeOIMod, modulesMut#i, currentGB);

            if n > 0 then (
                currentSymbolPlusOne := getSymbol concatenate(e, toString(i + 1));
                modulesMut#(i + 1) = makeFreeOIModule(freeOIMod.polyOIAlg, currentSymbolPlusOne, {}, DegreeShifts => {}); -- Zero module
                ddMut#(i + 1) = makeFreeOIModuleMap(modulesMut#i, modulesMut#(i + 1), {}) -- Zero map
            );

            break
        );

        currentGB = syzGens;
        currentFreeOIMod0 := freeOIModuleFromElement syzGens#0;
        currentFreeOIMod := makeFreeOIModule(currentFreeOIMod0.polyOIAlg, currentFreeOIMod0.basisSym, currentFreeOIMod0.genWidths, DegreeShifts => currentFreeOIMod0.degShifts);
        oldFomm := getMonomialOrder currentFreeOIMod0;
        newFomm := makeFreeOIModuleMap(target oldFomm, currentFreeOIMod, oldFomm.genImages);
        installSchreyerMonomialOrder newFomm;
        modulesMut#i = currentFreeOIMod;
        ddMut#i = newFomm
    );

    -- Minimize the resolution
    if #ddMut > 1 and not (#ddMut == 2 and isZero ddMut#1) and isHomogeneous ddMut#0 and not opts.FastNonminimal then (
        if opts.Verbose then print "----------------------------------------\n----------------------------------------\nMinimizing resolution...";
        done := false;
        while not done do (
            done = true;

            -- Look for units on identity basis elements
            unitFound := false;
            local data;
            for i from 1 to #ddMut - 1 do (
                ddMap := ddMut#i;
                if isZero ddMap then continue; -- Skip any zero maps
                srcMod := source ddMap;
                targMod := target ddMap;
                for j to #ddMap.genImages - 1 do (
                    if isZero ddMap.genImages#j then continue;
                    oiTerms := getOITermsFromVector(ddMap.genImages#j, Combine => true);
                    for term in oiTerms do (
                        b := term.basisIndex;
                        if b.oiMap.assignment === toList(1..b.oiMap.Width) then
                            if isUnit term.ringElement then (
                                unitFound = true;
                                done = false;
                                data = {i, j, term};
                                if opts.Verbose then print("Unit found on term: "|net term);
                                break
                            );
                        if unitFound then break
                    );
                    if unitFound then break
                );
                if unitFound then break
            );
            
            -- Prune the sequence
            if unitFound then (
                term := data#2;
                targBasisIdx := term.basisIndex.idx - 1; -- Recall idx's start at 1
                srcBasisIdx := data#1;
                ddMap := ddMut#(data#0);
                srcMod := source ddMap;
                targMod := target ddMap;

                if opts.Verbose then print "Pruning...";

                -- Compute the new modules
                newSrcMod := makeFreeOIModule(srcMod.polyOIAlg, srcMod.basisSym, remove(srcMod.genWidths, srcBasisIdx), DegreeShifts => remove(srcMod.degShifts, srcBasisIdx));
                newTargMod := makeFreeOIModule(targMod.polyOIAlg, targMod.basisSym, remove(targMod.genWidths, targBasisIdx), DegreeShifts => remove(targMod.degShifts, targBasisIdx));
                
                -- Compute the new differential
                newGenImages := new MutableList;
                if not (isZero newSrcMod or isZero newTargMod) then (
                    k := 0;
                    targBasisOIMap := makeOIMap(targMod.genWidths#targBasisIdx, toList(1..targMod.genWidths#targBasisIdx));
                    srcBasisOIMap := makeOIMap(srcMod.genWidths#srcBasisIdx, toList(1..srcMod.genWidths#srcBasisIdx));
                    for i to #srcMod.genWidths - 1 do (
                        if i == srcBasisIdx then continue;
                        oiTerms := getOITermsFromVector(ddMap.genImages#i, Combine => true);
                        stuff := 0_(getFreeModuleInWidth(srcMod, srcMod.genWidths#i));
                        oiMaps := getOIMaps(targMod.genWidths#targBasisIdx, srcMod.genWidths#i);

                        -- Calculate the stuff to subtract off
                        if #oiMaps > 0 and #oiTerms > 0 then
                            for term in oiTerms do (
                                b := term.basisIndex;
                                if not b.idx == targBasisIdx + 1 then continue;
                                if not b.oiMap.Width == srcMod.genWidths#i then continue;

                                local oiMap;
                                for oimap in oiMaps do
                                    if b.oiMap === composeOIMaps(oimap, targBasisOIMap) then (oiMap = oimap; break);
                                                                
                                modMap := getInducedModuleMap(srcMod, oiMap);
                                basisElt := getVectorFromOITerms {makeBasisElement makeBasisIndex(srcMod, srcBasisOIMap, srcBasisIdx + 1)};
                                stuff = stuff + term.ringElement * modMap basisElt
                            );

                        -- Calculate the new image
                        basisElt := getVectorFromOITerms {makeBasisElement makeBasisIndex(srcMod, makeOIMap(srcMod.genWidths#i, toList(1..srcMod.genWidths#i)), i + 1)};
                        field := srcMod.polyOIAlg.baseField;
                        newGenImage0 := ddMap(basisElt - lift(1 // term.ringElement, field) * stuff);
                        newOITerms := getOITermsFromVector(newGenImage0, Combine => true);
                        newGenImage := 0_(getFreeModuleInWidth(newTargMod, widthOfElement newGenImage0));
                        if not isZero newGenImage0 then
                            for newTerm in newOITerms do (
                                idx := newTerm.basisIndex.idx;
                                if idx > targBasisIdx + 1 then idx = idx - 1;
                                newGenImage = newGenImage + getVectorFromOITerms {makeOITerm(newTerm.ringElement, makeBasisIndex(newTargMod, newTerm.basisIndex.oiMap, idx))}
                            );

                        newGenImages#k = newGenImage;
                        k = k + 1
                    )
                );

                ddMut#(data#0) = makeFreeOIModuleMap(newTargMod, newSrcMod, new List from newGenImages);
                modulesMut#(data#0) = newSrcMod;
                modulesMut#(data#0 - 1) = newTargMod;

                -- Adjust the adjacent differentials
                -- Below map
                ddMap = ddMut#(data#0 - 1);
                ddMut#(data#0 - 1) = makeFreeOIModuleMap(target ddMap, newTargMod, remove(ddMap.genImages, targBasisIdx)); -- Restriction

                -- Above map
                if data#0 < #ddMut - 1 then (
                    newGenImages = new MutableList;
                    ddMap = ddMut#(1 + data#0);
                    srcMod = source ddMap;
                    targMod = target ddMap;

                    if not (isZero srcMod or isZero targMod) then (
                        for i to #ddMap.genImages - 1 do (
                            oiTerms := getOITermsFromVector ddMap.genImages#i;
                            newTerms := new MutableList;
                            k := 0;
                            for term in oiTerms do (
                                idx := term.basisIndex.idx;
                                if idx == srcBasisIdx + 1 then continue; -- Projection
                                if idx > srcBasisIdx + 1 then idx = idx - 1; -- Relabel
                                newTerms#k = makeOITerm(term.ringElement, makeBasisIndex(newSrcMod, term.basisIndex.oiMap, idx));
                                k = k + 1;
                            );
                            
                            if isZero ddMap.genImages#i then newGenImages#i = ddMap.genImages#i else newGenImages#i = getVectorFromOITerms new List from newTerms
                        )
                    );

                    srcMod.monOrder#0 = Lex;
                    ddMut#(1 + data#0) = makeFreeOIModuleMap(newSrcMod, srcMod, new List from newGenImages)
                )
            )
        )
    );

    ret := new OIResolution from {dd => new List from ddMut, modules => new List from modulesMut};

    -- Store the resolution
    oiResCache#(L, n, opts.FastNonminimal, opts.MinimalOIGB) = ret;

    ret
)

-- PURPOSE: Verify that an OIResolution is a complex
-- INPUT: An OIResolution 'C'
-- OUTPUT: true if C is a complex, false otherwise
isComplex = method(TypicalValue => Boolean)
isComplex OIResolution := C -> (
    if #C.dd < 2 then error "Expected a sequence with at least 2 maps";

    -- Check if the maps compose to zero
    for i from 1 to #C.dd - 1 do (
        modMap0 := C.dd#(i - 1);
        modMap1 := C.dd#i;
        if isZero modMap0 or isZero modMap1 then continue;
        srcMod := source modMap1;
        basisElts := for i to #srcMod.genWidths - 1 list makeBasisElement makeBasisIndex(srcMod, makeOIMap(srcMod.genWidths#i, toList(1..srcMod.genWidths#i)), i + 1);
        for basisElt in basisElts do (
            result := modMap0 modMap1 getVectorFromOITerms {basisElt};
            if not isZero result then return false
        )
    );

    true
)

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- DOCUMENTATION ---------------------------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

beginDocumentation()

doc ///
    Key
        OIGroebnerBases
    Headline
        Computation in OI-modules over Noetherian polynomial OI-algebras
    Description
        Text
            This package allows one to compute Gröbner bases, syzygies and free resolutions for submodules of free OI-modules over Noetherian polynomial OI-algebras.
        
            Given a Noetherian polynomial OI-algebra $\mathbf{P} := (\mathbf{X}^{\text{OI},1})^{\otimes c}$ for some integer $c > 0$, one can consider free OI-modules $\mathbf{F} := \bigoplus_{i=1}^s\mathbf{F}^{\text{OI}, d_i}$ over $\mathbf{P}$ for integers $d_i\geq 0$. If $\mathbf{M}$ is a $\mathbf{P}$-submodule of $\mathbf{F}$ generated by $B=\{b_1,\ldots,b_t\}$, then a finite Gröbner basis can be computed from $B$ using @TO oiGB@. Furthermore, one can compute syzygies and resolutions with respect to $B$ using @TO oiSyz@ and @TO oiRes@. In this documentation we often use the terms OI-Gröbner basis and Gröbner basis interchangeably.
        
            For an introduction to the theory of OI-modules and OI-resolutions, we refer the reader to the @TO "Bibliography"@.
    Subnodes
        :Polynomial OI-algebras
        PolynomialOIAlgebra
        makePolynomialOIAlgebra
        getAlgebraInWidth
        (net,PolynomialOIAlgebra)
        (toString,PolynomialOIAlgebra)
        (symbol _,PolynomialOIAlgebra,ZZ)
        :Free OI-modules
        FreeOIModule
        makeFreeOIModule
        getFreeModuleInWidth
        (net,FreeOIModule)
        (toString,FreeOIModule)
        (symbol _,FreeOIModule,ZZ)
        getGenWidths
        DegreeShifts
        getDegShifts
        installBasisElements
        makeMonic
        freeOIModuleFromElement
        :Maps between free OI-modules
        FreeOIModuleMap
        makeFreeOIModuleMap
        (net,FreeOIModuleMap)
        (symbol SPACE,FreeOIModuleMap,List)
        (isHomogeneous,FreeOIModuleMap)
        (source,FreeOIModuleMap)
        (target,FreeOIModuleMap)
        :Algorithms
        oiGB
        isOIGB
        oiSyz
        MinimalOIGB
        :OI-resolutions
        OIResolution
        oiRes
        isComplex
        (describe,OIResolution)
        (net,OIResolution)
        (symbol _,OIResolution,ZZ)
        :Miscellaneous
        "Bibliography"
///

doc ///
    Key
        "Bibliography"
    Headline
        Bibliography for the OIGroebnerBases package
    Description
        Text
            [NR] U. Nagel and T. Römer, {\it FI- and OI-modules with varying coefficients}, J. Algebra {\bf 535} (2019), 286-322.

            [FN] N. Fieldsteel and U. Nagel, {\it Minimal and cellular free resolutions over polynomial OI-algebras}, Preprint, arXiv:2105.08603, 2021.
///

doc ///
    Key
        PolynomialOIAlgebra
    Headline
        The class of all Noetherian polynomial OI-algebras over a field
    Description
        Text
            This type implements OI-algebras of the form $(\mathbf{X}^{\text{OI},1})^{\otimes c}$ for some integer $c>0$. To make a new @TT "PolynomialOIAlgebra"@ use @TO makePolynomialOIAlgebra@. To get the $K$-algebra in a specific width of a polynomial OI-algebra, use @TO getAlgebraInWidth@.

            Each @TT "PolynomialOIAlgebra"@ object carries the lexicographic monomial order determined by $x_{i,j}>x_{i',j'}$ iff $j>j'$ or $j=j'$ and $i>i'$.
///

doc ///
    Key
        makePolynomialOIAlgebra
        (makePolynomialOIAlgebra,Ring,ZZ,Symbol)
    Headline
        Make a new PolynomialOIAlgebra object
    Usage
        makePolynomialOIAlgebra(K,c,x)
    Inputs
        K:Ring
        c:ZZ
        x:Symbol
    Outputs
        :PolynomialOIAlgebra
    Description
        Text
            Makes a new @TO PolynomialOIAlgebra@ object implementing the functor $(\mathbf{X}^{\text{OI}, 1})^{\otimes c}$ over $K$ with variables in $x$.
        Example
            P = makePolynomialOIAlgebra(QQ,1,x)
            Q = makePolynomialOIAlgebra(QQ,2,y)
///

doc ///
    Key
        getAlgebraInWidth
        (getAlgebraInWidth,PolynomialOIAlgebra,ZZ)
    Headline
        Get the $K$-algebra in a specified width of a polynomial OI-algebra
    Usage
        getAlgebraInWidth(P,n)
    Inputs
        P:PolynomialOIAlgebra
        n:ZZ
    Outputs
        :PolynomialRing
    Description
        Text
            Returns the width $n$ component of a @TO PolynomialOIAlgebra@ object.
        Example
            P = makePolynomialOIAlgebra(QQ,1,x);
            getAlgebraInWidth(P, 3)
            Q = makePolynomialOIAlgebra(QQ,2,y);
            getAlgebraInWidth(Q, 4)            
///

doc ///
    Key
        (toString,PolynomialOIAlgebra)
    Headline
        Convert a PolynomialOIAlgebra object to a string
    Usage
        toString P
    Inputs
        P:PolynomialOIAlgebra
    Outputs
        :String
    Description
        Text
            Outputs the base field, number of variable rows and variable symbol of a @TO PolynomialOIAlgebra@ object.
        Example
            Q = makePolynomialOIAlgebra(QQ,2,y);
            toString Q
///

doc ///
    Key
        (net,PolynomialOIAlgebra)
    Headline
        Display extended information about a PolynomialOIAlgebra object
    Usage
        net P
    Inputs
        P:PolynomialOIAlgebra
    Outputs
        :Net
    Description
        Text
            Outputs the base field, number of variable rows and variable symbol of a @TO PolynomialOIAlgebra@ object in extended format.
        Example
            Q = makePolynomialOIAlgebra(QQ,2,y);
            net Q
///

doc ///
    Key
        (symbol _,PolynomialOIAlgebra,ZZ)
    Headline
        Get the $K$-algebra in a specified width of a polynomial OI-algebra
    Usage
        P_n
    Inputs
        P:PolynomialOIAlgebra
        n:ZZ
    Outputs
        :PolynomialRing
    Description
        Text
            This is a shortcut version of @TO getAlgebraInWidth@.
        Example
            Q = makePolynomialOIAlgebra(QQ,2,y);
            Q_4
///

doc ///
    Key
        FreeOIModule
    Headline
        The class of all free OI-modules over a polynomial OI-algebra
    Description
        Text
            This type implements free OI-modules $\mathbf{F} := \bigoplus_{i=1}^s\mathbf{F}^{\text{OI}, d_i}$ over a @TO PolynomialOIAlgebra@ object $\mathbf{P}$ for integers $d_i\geq 0$. To make a new @TT "FreeOIModule"@ object use @TO makeFreeOIModule@. To get the free module in a specific width of a free OI-module, use @TO getFreeModuleInWidth@. One may also obtain the generator widths and degree shifts using @TO getGenWidths@ and @TO getDegShifts@ respectively.

            Each @TT "FreeOIModule"@ object carries either the @TO Lex@ monomial order determined by the monomial order of $\mathbf{P}$, or a Schreyer monomial order induced by a @TO FreeOIModuleMap@.
///

doc ///
    Key
        makeFreeOIModule
        (makeFreeOIModule,PolynomialOIAlgebra,Symbol,List)
        [makeFreeOIModule,DegreeShifts]
    Headline
        Make a new FreeOIModule object
    Usage
        makeFreeOIModule(P, e, W)
    Inputs
        P:PolynomialOIAlgebra
        e:Symbol
        W:List
    Outputs
        :FreeOIModule
    Description
        Text
            Makes a new @TO FreeOIModule@ object over the @TO PolynomialOIAlgebra@ $\mathbf{P}$ with basis symbol $e$ and generator widths given by @TT "W"@.

            The option @TT "DegreeShifts"@ allows one to specify a shift of grading.
        Example
            P = makePolynomialOIAlgebra(QQ,1,x);
            F = makeFreeOIModule(P, e, {1,2}, DegreeShifts => {-3,-2})
///

doc ///
    Key
        getFreeModuleInWidth
        (getFreeModuleInWidth,FreeOIModule,ZZ)
    Headline
        Get the free module in a specified width of a free OI-module
    Usage
        getFreeModuleInWidth(F, n)
    Inputs
        F:FreeOIModule
        n:ZZ
    Outputs
        :Module
    Description
        Text
            Returns the width $n$ component of a @TO FreeOIModule@ object.
        Example
            P = makePolynomialOIAlgebra(QQ,1,x);
            F = makeFreeOIModule(P, e, {1,2}, DegreeShifts => {-3,-2});
            getFreeModuleInWidth(F, 1)
            getFreeModuleInWidth(F, 3)
///

doc ///
    Key
        (toString,FreeOIModule)
    Headline
        Convert a FreeOIModule object to a string
    Usage
        toString F
    Inputs
        F:FreeOIModule
    Outputs
        :String
    Description
        Text
            Outputs the generator widths and degree shifts of a @TO FreeOIModule@ object.
        Example
            P = makePolynomialOIAlgebra(QQ,1,x);
            F = makeFreeOIModule(P, e, {1,2}, DegreeShifts => {-3,-2});
            toString F
///

doc ///
    Key
        (net,FreeOIModule)
    Headline
        Display extended information about a FreeOIModule object
    Usage
        net F
    Inputs
        F:FreeOIModule
    Outputs
        :Net
    Description
        Text
            Outputs the underlying @TO PolynomialOIAlgebra@ object, the basis symbol, the generator widths, the degree shifts and the monomial order of a @TO FreeOIModule@ object.
        Example
            P = makePolynomialOIAlgebra(QQ,1,x);
            F = makeFreeOIModule(P, e, {1,2}, DegreeShifts => {-3,-2});
            net F
///

doc ///
    Key
        getGenWidths
        (getGenWidths,FreeOIModule)
    Usage
        getGenWidths F
    Inputs
        F:FreeOIModule
    Outputs
        :List
    Description
        Text
            Outputs the @TO List@ of generator widths of a @TO FreeOIModule@ object.
        Example
            P = makePolynomialOIAlgebra(QQ,1,x);
            F = makeFreeOIModule(P, e, {1,2}, DegreeShifts => {-3,-2});
            getGenWidths F
///

doc ///
    Key
        getDegShifts
        (getDegShifts,FreeOIModule)
    Usage
        getDegShifts F
    Inputs
        F:FreeOIModule
    Outputs
        :List
    Description
        Text
            Outputs the @TO List@ of degree shifts of a @TO FreeOIModule@ object.
        Example
            P = makePolynomialOIAlgebra(QQ,1,x);
            F = makeFreeOIModule(P, e, {1,2}, DegreeShifts => {-3,-2});
            getDegShifts F
///

doc ///
    Key
        (symbol _,FreeOIModule,ZZ)
    Usage
        F_n
    Inputs
        F:FreeOIModule
        n:ZZ
    Outputs
        :Module
    Description
        Text
            This is a shortcut version of @TO getFreeModuleInWidth@.
        Example
            P = makePolynomialOIAlgebra(QQ,1,x);
            F = makeFreeOIModule(P, e, {1,2}, DegreeShifts => {-3,-2});
            F_1
            F_3         
///

doc ///
    Key
        installBasisElements
        (installBasisElements,FreeOIModule,ZZ)
    Usage
        installBasisElements(F,n)
    Inputs
        F:FreeOIModule
        n:ZZ
    Description
        Text
            Suppose $\mathbf{F}$ is a free OI-module with basis symbol $e$ and generator widths $\{d_1=1,d_2=2\}$. Then the local basis elements in width $n$ are represented as @TT "e_(n,{...},i)"@ where @TT "{...}"@ describes an OI-morphism from $[d_i]$ to $[n]$. For example, $e_{(5,\{2,4\},2)}$ is the local basis element in $\mathbf{F}_5$ given by $$\mathbf{F}(\pi)(e_{\text{id}_{[d_2]=[2]}})$$ where $\pi:[2]\to[5]$ is the OI-morphism with $1\mapsto2$ and $2\mapsto4$.
            This method assigns the @TO IndexedVariable@s @TT "e_(n,{...},i)"@ to the appropriate basis elements of $\mathbf{F}_n$ so that the user may access them.
        Example
            P = makePolynomialOIAlgebra(QQ,1,x);
            F = makeFreeOIModule(P, e, {1,2}, DegreeShifts => {-3,-2});
            installBasisElements(F, 5);
            e_(5,{2,4},2)
            F_5; x_(1,5)*e_(5,{2,4},2)+x_(1,4)^2*e_(5,{3},1)
///

doc ///
    Key
        makeMonic
        (makeMonic,List)
    Headline
        Make a list of elements of a FreeOIModule monic
    Usage
        makeMonic L
    Inputs
        L:List
    Outputs
        :List
    Description
        Text
            Given a @TO List@ of elements of a @TO FreeOIModule@, this method makes each element have a lead coefficient of $1$.
        Example
            P = makePolynomialOIAlgebra(QQ,1,x);
            F = makeFreeOIModule(P, e, {1,2}, DegreeShifts => {-3,-2});
            installBasisElements(F, 5);
            F_5; b = x_(1,5)*e_(5,{2,4},2)+3*x_(1,4)^2*e_(5,{3},1);
            makeMonic {b}
///

doc ///
    Key
        FreeOIModuleMap
    Headline
        The class of all maps between FreeOIModule objects
    Description
        Text
            This type implements maps $\varphi:\mathbf{F}\to\mathbf{G}$ between @TO FreeOIModule@ objects $\mathbf{F}$ and $\mathbf{G}$. To make a new @TT "FreeOIModuleMap"@ use @TO makeFreeOIModuleMap@. To get the source and target of a @TT "FreeOIModuleMap"@ use @TO (source,FreeOIModuleMap)@ and @TO (target,FreeOIModuleMap)@ respectively.
///

doc ///
    Key
        makeFreeOIModuleMap
        (makeFreeOIModuleMap,FreeOIModule,FreeOIModule,List)
    Headline
        Make a map between two FreeOIModules
    Usage
        makeFreeOIModuleMap(G, F, L)
    Inputs
        G:FreeOIModule
        F:FreeOIModule
        L:List
    Outputs
        :FreeOIModuleMap
    Description
        Text
            A map of free OI-modules $\varphi:\mathbf{F}\to\mathbf{G}$ is determined by its action on the basis of $\mathbf{F}$. The @TO List@ @TT "L"@ is used to specify where these basis elements are sent.
        Example
            P = makePolynomialOIAlgebra(QQ,1,x);
            G = makeFreeOIModule(P, e, {1,2}, DegreeShifts => {-3,-2});
            installBasisElements(G, 5);
            G_5; b = x_(1,5)*e_(5,{2,4},2)+3*x_(1,4)^2*e_(5,{3},1);
            F = makeFreeOIModule(P, d, {5});
            f = makeFreeOIModuleMap(G, F, {b})
        Text
            In the above example, the basis element of $\mathbf{F}$ is sent to $b$ under the action of $f$.  
///

doc ///
    Key
        (source,FreeOIModuleMap)
    Headline
        Get the source of a FreeOIModuleMap
    Usage
        source f
    Inputs
        f:FreeOIModuleMap
    Outputs
        :FreeOIModule
    Description
        Text
            Returns the @TO source@ of a @TO FreeOIModuleMap@ object.
        Example
            P = makePolynomialOIAlgebra(QQ,1,x);
            G = makeFreeOIModule(P, e, {1,2}, DegreeShifts => {-3,-2});
            installBasisElements(G, 5);
            G_5; b = x_(1,5)*e_(5,{2,4},2)+3*x_(1,4)^2*e_(5,{3},1);
            F = makeFreeOIModule(P, d, {5});
            f = makeFreeOIModuleMap(G, F, {b});
            source f
///

doc ///
    Key
        (target,FreeOIModuleMap)
    Headline
        Get the target of a FreeOIModuleMap
    Usage
        target f
    Inputs
        f:FreeOIModuleMap
    Outputs
        :FreeOIModule
    Description
        Text
            Returns the @TO target@ of a @TO FreeOIModuleMap@ object.
        Example
            P = makePolynomialOIAlgebra(QQ,1,x);
            G = makeFreeOIModule(P, e, {1,2}, DegreeShifts => {-3,-2});
            installBasisElements(G, 5);
            G_5; b = x_(1,5)*e_(5,{2,4},2)+3*x_(1,4)^2*e_(5,{3},1);
            F = makeFreeOIModule(P, d, {5});
            f = makeFreeOIModuleMap(G, F, {b});
            target f
///

doc ///
    Key
        (net,FreeOIModuleMap)
    Headline
        Display extended information for a FreeOIModuleMap object
    Usage
        net f
    Inputs
        f:FreeOIModuleMap
    Outputs
        :Net
    Description
        Text
            Outputs the source module, target module and list of generator images for a @TO FreeOIModuleMap@ object.
        Example
            P = makePolynomialOIAlgebra(QQ,1,x);
            G = makeFreeOIModule(P, e, {1,2}, DegreeShifts => {-3,-2});
            installBasisElements(G, 5);
            G_5; b = x_(1,5)*e_(5,{2,4},2)+3*x_(1,4)^2*e_(5,{3},1);
            F = makeFreeOIModule(P, d, {5});
            f = makeFreeOIModuleMap(G, F, {b});
            net f 
///

doc ///
    Key
        (symbol SPACE,FreeOIModuleMap,List)
    Headline
        Apply a FreeOIModuleMap to a List of elements
    Usage
        f L
    Inputs
        f:FreeOIModuleMap
        L:List
    Outputs
        :List
    Description
        Text
            Given a @TO FreeOIModuleMap@ $\varphi:\mathbf{F}\to\mathbf{G}$ and a finite subset $L\subset\mathbf{F}$, computes $\varphi(L)$.
        Example
            P = makePolynomialOIAlgebra(QQ,1,x);
            G = makeFreeOIModule(P, e, {1,2}, DegreeShifts => {-3,-2});
            installBasisElements(G, 5);
            G_5; b = x_(1,5)*e_(5,{2,4},2)+3*x_(1,4)^2*e_(5,{3},1);
            F = makeFreeOIModule(P, d, {5});
            f = makeFreeOIModuleMap(G, F, {b});
            installBasisElements(F, 5);
            F_5; a = d_(5,{1,2,3,4,5},1);
            f {a, x_(1,4)*x_(1,3)*a}
///

doc ///
    Key
        (isHomogeneous,FreeOIModuleMap)
    Headline
        Check if a FreeOIModuleMap is homogeneous
    Usage
        isHomogeneous f
    Inputs
        f:FreeOIModuleMap
    Outputs
        :Boolean
    Description
        Text
            Checks if a @TO FreeOIModuleMap@ $\varphi:\mathbf{F}\to\mathbf{G}$ is graded.
        Example
            P = makePolynomialOIAlgebra(QQ,1,x);
            G = makeFreeOIModule(P, e, {1,2}, DegreeShifts => {-3,-2});
            installBasisElements(G, 5);
            G_5; b = x_(1,5)^2*e_(5,{2,4},2)+3*x_(1,4)*e_(5,{3},1);
            degree b
            F = makeFreeOIModule(P, d, {5}, DegreeShifts => {-4});
            f = makeFreeOIModuleMap(G, F, {b});
            isHomogeneous f
        Text
            In the above example, $f$ maps the degree $4$ basis element of $\mathbf{F}$ to the degree $4$ homogeneous element $b$ of $\mathbf{G}$ and is therefore a graded map.
///

doc ///
    Key
        MinimalOIGB
    Headline
        Option for minimal Gröbner bases
    Description
        Text
            If @TT "MinimalOIGB => false"@ is given, then the algorithm will not take the extra steps to remove redundant elements from the basis. Note that by "minimal" we mean minimal as a Gröbner basis, not necessarily as a generating set.

            If @TT "MinimalOIGB => true"@ is given then the algorithm will minimize the Gröbner basis.
        Example
            P = makePolynomialOIAlgebra(QQ,1,x);
            F = makeFreeOIModule(P, e, {1});
            installBasisElements(F, 1);
            installBasisElements(F, 2);
            F_1; b1 = x_(1,1)^3*e_(1,{1},1);
            F_2; b2 = x_(1,1)^2*e_(2,{1},1); b3 = x_(1,2)^2*e_(2,{2},1); b4 = x_(1,1)*x_(1,2)*e_(2,{2},1);
            B = oiGB {b1, b2, b3, b4}
            oiSyz(B, d)
            oiSyz(B, d, MinimalOIGB => false)
///

doc ///
    Key
        DegreeShifts
    Headline
        Option for makeFreeOIModule
    Description
        Text
            This is an @TO Option@ for the @TO makeFreeOIModule@ method. It allows one to specify a shift of grading when construction a free OI-module.
        Example
            P = makePolynomialOIAlgebra(QQ,1,x);
            F = makeFreeOIModule(P, e, {1,2}, DegreeShifts => {-3,-2})
///

doc ///
    Key
        oiSyz
        (oiSyz,List,Symbol)
        [oiSyz,Verbose]
        [oiSyz,MinimalOIGB]
    Headline
        Compute the module of syzygies of a finite Gröbner basis
    Usage
        oiSyz(B, d)
    Inputs
        B:List
        d:Symbol
    Outputs
        :List
    Description
        Text
            Given a finite OI-Gröbner basis $B$, this method will use an OI-analogue of Schreyer's Theorem to compute a finite Gröbner basis for the module of syzygies of $B$ using the basis symbol $d$.

            If the option @TT "MinimalOIGB => false"@ is given, then the algorithm will not take the extra steps to remove redundant elements from the basis. Note that by "minimal" we mean minimal as a Gröbner basis, not necessarily as a generating set.
        
            The option @TT "Verbose => true"@ will output (a lot) of debug information.
        Example
            P = makePolynomialOIAlgebra(QQ,1,x);
            G = makeFreeOIModule(P, e, {1});
            installBasisElements(G, 1);
            installBasisElements(G, 2);
            G_1; b1 = x_(1,1)^3*e_(1,{1},1);
            G_2; b2 = x_(1,1)^2*e_(2,{1},1); b3 = x_(1,2)^2*e_(2,{2},1); b4 = x_(1,1)*x_(1,2)*e_(2,{2},1);
            B = oiGB {b1, b2, b3, b4}
            C = oiSyz(B, d)
        Text
            Note that in the above example, the $b_i$ are all monomials so @TO oiGB@ doesn't actually do anything.
///

doc ///
    Key
        isOIGB
        (isOIGB,List)
        [isOIGB,Verbose]
    Headline
        Check if a subset is an OI-Gröbner basis
    Usage
        isOIGB B
    Inputs
        B:List
    Outputs
        :Boolean
    Description
        Text
            Uses an OI-analogue of Buchberger's Criterion to determine if $B$ is an OI-Gröbner basis.
        Example
            P = makePolynomialOIAlgebra(QQ,1,x);
            F = makeFreeOIModule(P, e, {1});
            installBasisElements(F, 1);
            installBasisElements(F, 2);
            F_1; f = x_(1,1)^3*e_(1,{1}, 1);
            F_2; h = x_(1,2)^2*e_(2, {2}, 1) + x_(1,1)*x_(1,2)*e_(2, {2}, 1);
            B = oiGB {f, h}
            isOIGB B
///

doc ///
    Key
        OIResolution
    Headline
        The class of all OI-resolutions of submodules of free OI-modules
    Description
        Text
            This type implements OI-resolutions for submodules of free OI-modules. To make a new @TT "OIResolution"@ object, use @TO oiRes@. To verify that an OI-resolution is a complex, use @TO isComplex@. Given an @TT "OIResolution"@ object @TT "C"@, one can view the differentials via @TT "C.dd"@. Furthermore, the $i^{\text{th}}$ module in the sequence may be accessed with @TT "C_i"@. To view more information about an OI-resolution, use @TO (describe,OIResolution)@.
///

doc ///
    Key
        oiRes
        (oiRes,List,ZZ)
        [oiRes,FastNonminimal]
        [oiRes,MinimalOIGB]
        [oiRes,Verbose]
    Headline
        Compute an OI-resolution for a submodule of a free OI-module
    Usage
        oiRes(B, n)
    Inputs
        B:List
        n:ZZ
    Outputs
        :OIResolution
    Description
        Text
            Suppose $B$ is a generating set of a submodule of a free OI-module $\mathbf{F}$. This method computes a length $n$ OI-resolution of the module generated by $B$ by iterating the @TO oiSyz@ method.

            If $B$ consists of homogeneous elements and the option @TT "FastNonminimal => false"@ is given (which it is by default) then the maps in the sequence will be minimized (in the sense of Definition 3.1 of @TO2{"Bibliography","[FN]"}@).

            If the option @TT "MinimalOIGB => false"@ is given, then the algorithm will not take the extra steps to remove redundant elements from the basis. Note that by "minimal" we mean minimal as a Gröbner basis, not necessarily as a generating set.

            The option @TT "Verbose => true"@ will output (a lot) of debug information.
        Example
            P = makePolynomialOIAlgebra(QQ,1,x);
            F = makeFreeOIModule(P, e, {1});
            installBasisElements(F, 1);
            installBasisElements(F, 2);

            F_1; b1 = x_(1,1)*e_(1,{1},1); b2 = x_(1,1)^2*e_(1,{1},1);
            F_2; b3 = x_(1,2)*e_(2,{1},1);
            oiRes({b1, b2, b3}, 1)
            oiRes({b1, b2, b3}, 1, MinimalOIGB => false)
    Caveat
        Even though the maps in the sequence are minimized, the $n^{\text{th}}$ module in the sequence may not have minimal rank since the $(n+1)^{\text{st}}$ map (which has not been computed yet) may not be minimal.
///

doc ///
    Key
        (symbol _,OIResolution,ZZ)
    Headline
        Get the $n^{\text{th}}$ module in an OI-resolution
    Usage
        C_n
    Inputs
        C:OIResolution
        n:ZZ
    Outputs
        :FreeOIModule
    Description
        Text
            If $C:\cdots\to\mathbf{F}_2\to\mathbf{F}_1\to\mathbf{F}_0$ is some OI-resolution, this method returns $\mathbf{F}_n$.
        Example
            P = makePolynomialOIAlgebra(QQ,1,x);
            F = makeFreeOIModule(P, e, {1});
            installBasisElements(F, 1);
            installBasisElements(F, 2);

            F_1; b1 = x_(1,1)*e_(1,{1},1); b2 = x_(1,1)^2*e_(1,{1},1);
            F_2; b3 = x_(1,2)*e_(2,{1},1);
            C = oiRes({b1, b2, b3}, 1, MinimalOIGB => false);
            C_0
            C_1
///

doc ///
    Key
        (describe,OIResolution)
    Headline
        Display the modules and maps in an OI-resolution
    Usage
        describe C
    Inputs
        C:OIResolution
    Outputs
        :Net
    Description
        Text
            Displays the modules and differentials in an OI-resolution.
        Example
            P = makePolynomialOIAlgebra(QQ,1,x);
            F = makeFreeOIModule(P, e, {1});
            installBasisElements(F, 1);
            installBasisElements(F, 2);

            F_1; b1 = x_(1,1)*e_(1,{1},1); b2 = x_(1,1)^2*e_(1,{1},1);
            F_2; b3 = x_(1,2)*e_(2,{1},1);
            C = oiRes({b1, b2, b3}, 1, MinimalOIGB => false);
            describe C
///

doc ///
    Key
        (net,OIResolution)
    Headline
        Display extended information about an OIResolution object
    Usage
        net C
    Inputs
        C:OIResolution
    Outputs
        :Net
    Description
        Text
            Displays the modules in an OI-resolution.
        Example
            P = makePolynomialOIAlgebra(QQ,1,x);
            F = makeFreeOIModule(P, e, {1});
            installBasisElements(F, 1);
            installBasisElements(F, 2);

            F_1; b1 = x_(1,1)*e_(1,{1},1); b2 = x_(1,1)^2*e_(1,{1},1);
            F_2; b3 = x_(1,2)*e_(2,{1},1);
            C = oiRes({b1, b2, b3}, 1, MinimalOIGB => false);
            net C
///

doc ///
    Key
        isComplex
        (isComplex,OIResolution)
    Headline
        Checks if the differentials in an OI-resolution compose to zero
    Usage
        isComplex C
    Inputs
        C:OIResolution
    Outputs
        :Boolean
    Description
        Text
            Given an @TO OIResolution@ object @TT "C"@ with at least two maps in the sequence, this method checks if @TT "CC.dd_i CC.dd_(i+1) = 0"@ for all $i$.
        Example
            P = makePolynomialOIAlgebra(QQ,1,x);
            F = makeFreeOIModule(P, e, {1});
            installBasisElements(F, 1);
            installBasisElements(F, 2);

            F_1; b1 = x_(1,1)*e_(1,{1},1); b2 = x_(1,1)^2*e_(1,{1},1);
            F_2; b3 = x_(1,2)*e_(2,{1},1);
            C = oiRes({b1, b2, b3}, 1, MinimalOIGB => false)
            isComplex C
///

doc ///
    Key
        freeOIModuleFromElement
        (freeOIModuleFromElement,Vector)
    Headline
        Get the FreeOIModule containing a Vector
    Usage
        freeOIModuleFromElement f
    Inputs
        f:Vector
    Outputs
        :FreeOIModule
    Description
        Text
            If $f$ is an element of a free OI-module $\mathbf{F}$, this method returns $\mathbf{F}$.
        Example
            P = makePolynomialOIAlgebra(QQ,1,x);
            F = makeFreeOIModule(P, e, {1});
            installBasisElements(F, 1);
            installBasisElements(F, 2);

            F_1; b1 = x_(1,1)*e_(1,{1},1); b2 = x_(1,1)^2*e_(1,{1},1);
            freeOIModuleFromElement b1
    Caveat
        This method will error if the input is a @TO Vector@ not belonging to any @TO FreeOIModule@.
///

doc ///
    Key
        oiGB
        (oiGB,List)
        [oiGB,Verbose]
        [oiGB,Strategy]
        [oiGB,MinimalOIGB]
    Headline
        Compute a Gröbner basis for a finitely generated $\mathbf{P}$-submodule of $\mathbf{F}$
    Usage
        oiGB B
    Inputs
        B:List
    Outputs
        :List
    Description
        Text
            Uses an OI-analogue of Buchberger's Algorithm to produce a finite Gröbner basis from a given generating set $B=\{b_1,\ldots,b_t\}$ of some $\mathbf{P}$-submodule of $\mathbf{F}$. The algorithm uses the monomial order specified by $\mathbf{F}$, see @TO FreeOIModule@ for more details.
            
            If the option @TT "MinimalOIGB => false"@ is given, then the algorithm will not take the extra steps to remove redundant elements from the basis. Note that by "minimal" we mean minimal as a Gröbner basis, not necessarily as a generating set.
            
            The option @TT "Verbose => true"@ will output (a lot) of debug information.

            If @TT "Strategy => 2"@ is given, then the algorithm will append all nonzero remainders to the basis on a given step before moving to the next step. This can sometimes improve performance, but most of the time the default option @TT "Strategy => 1"@ seems to be faster, which appends only a single nonzero remainder to the basis before moving on to the next step.
        Example
            P = makePolynomialOIAlgebra(QQ,1,x);
            F = makeFreeOIModule(P, e, {1});
            installBasisElements(F, 1);
            installBasisElements(F, 2);
            F_1; b1 = x_(1,1)*e_(1,{1},1);
            F_2; b2 = x_(1,2)*e_(2,{1},1) + x_(1,1)*e_(2,{2},1);
            L = oiGB {b1, b2}
///

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- TESTS -----------------------------------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

-- Test 0: Compute a Groebner basis
TEST ///
P = makePolynomialOIAlgebra(QQ,1,x);
F = makeFreeOIModule(P, e, {1});
installBasisElements(F, 1);
installBasisElements(F, 2);
installBasisElements(F, 3);

F_1; f = x_(1,1)^3*e_(1,{1}, 1);
F_2; h = x_(1,2)^2*e_(2, {2}, 1) + x_(1,1)*x_(1,2)*e_(2, {2}, 1);
B = oiGB {f, h};

F_2; elt1 = x_(1,2)*x_(1,1)^2*e_(2,{2},1);
F_3; elt2 = (-x_(1,3)*x_(1,2)+x_(1,3)*x_(1,1))*e_(3,{3},1);

checkB = makeMonic B;
checkSet = makeMonic {f, h, elt1, elt2};
assert(set checkB === set checkSet)
///

-- Test 1: Compute first syzygies
TEST ///
P = makePolynomialOIAlgebra(QQ,1,x);
F = makeFreeOIModule(P, e, {1});
installBasisElements(F, 1);
installBasisElements(F, 2);

F_1; b1 = x_(1,1)^3*e_(1,{1},1);
F_2; b2 = x_(1,1)^2*e_(2,{1},1); b3 = x_(1,2)^2*e_(2,{2},1); b4 = x_(1,1)*x_(1,2)*e_(2,{2},1);
B = oiGB {b1, b2, b3, b4};
C = oiSyz(B, d);

G = freeOIModuleFromElement C#0;
installBasisElements(G, 2);
installBasisElements(G, 3);

G_2;
width2stuff = {
d_(2,{1},1)-x_(1,1)*d_(2,{1,2},2),
x_(1,1)*d_(2,{1,2},3)-x_(1,2)*d_(2,{1,2},4),
d_(2,{2},1)-x_(1,2)*d_(2,{1,2},3)
};

G_3;
width3stuff = {
-d_(3,{1,3},2)+d_(3,{1,2},2),
d_(3,{2,3},2)-d_(3,{1,2},3),
x_(1,1)*d_(3,{2,3},4)-x_(1,2)*d_(3,{1,3},4),
-d_(3,{2,3},3)+d_(3,{1,3},3),
x_(1,2)*d_(3,{1,3},3)-x_(1,3)*d_(3,{2,3},4)
};

checkC = makeMonic C;
checkSet = makeMonic join(width2stuff, width3stuff);
assert(set checkC === set checkSet)
///

-- Test 2: Compute length 1 resolution
TEST ///
P = makePolynomialOIAlgebra(QQ,1,x);
F = makeFreeOIModule(P, e, {1});
installBasisElements(F, 1);
installBasisElements(F, 2);
F_1; b1 = x_(1,1)*e_(1,{1},1); b2 = x_(1,1)^2*e_(1,{1},1);
F_2; b3 = x_(1,2)*e_(2,{1},1);
C = oiRes({b1, b2, b3}, 1, MinimalOIGB => false);
assert isComplex C;
assert(getGenWidths C_1 == {2,2,3,3});
assert(getDegShifts C_1 == {-2,-3,-2,-2})
///

end

-- Scratch work 

load "OIGroebnerBases.m2"
P = makePolynomialOIAlgebra(QQ,1,x);
F = makeFreeOIModule(P, e, {1,1,2});
installBasisElements(F, 1);
installBasisElements(F, 2);
F_1; b1 = x_(1,1)*e_(1,{1},1)+x_(1,1)*e_(1,{1},2);
F_2; b2 = x_(1,1)*e_(2,{2},2) + x_(1,2)*e_(2,{1,2},3); b3 = e_(2,{2},1);
C = oiRes({b1,b2,b3}, 1, Verbose => true)

restart
load "OIGroebnerBases.m2"
P = makePolynomialOIAlgebra(QQ,1,x);
F = makeFreeOIModule(P, e, {1});
installBasisElements(F, 1);
installBasisElements(F, 2);
installBasisElements(F, 3);
installBasisElements(F, 4);

-- Res example 1
F_1; b1 = x_(1,1)*e_(1,{1},1); b2 = x_(1,1)^2*e_(1,{1},1);
F_2; b3 = x_(1,2)*e_(2,{1},1);
C = oiRes({b1, b2, b3}, 1, Verbose => true)

-- Res example 2
F_1; b1 = x_(1,1)*e_(1,{1},1);
F_2; b2 = x_(1,2)*e_(2,{1},1);
C = oiRes({b1,b2}, 0, Verbose => true)

-- Syzygy example 1
F_1; b1 = x_(1,1)^3*e_(1,{1},1);
F_2; b2 = x_(1,1)^2*e_(2,{1},1); b3 = x_(1,2)^2*e_(2,{2},1); b4 = x_(1,1)*x_(1,2)*e_(2,{2},1);
B = oiGB({b1, b2, b3, b4}, Verbose => true)
C = oiSyz(B, d, Verbose => true)
isOIGB C

-- Syzygy example 2
F_1; f = x_(1,1)^3*e_(1,{1}, 1);
F_2; h = x_(1,2)^2*e_(2, {2}, 1) + x_(1,1)*x_(1,2)*e_(2, {2}, 1);
B = oiGB({f, h}, Verbose => true)
C = oiSyz(B, d, Verbose => true)
isOIGB C

-- Syzygy example 3
F_1; f = x_(1,1)^3*e_(1,{1}, 1);
F_2; h = x_(1,2)^2*e_(2, {2}, 1) + x_(1,1)*x_(1,2)*e_(2, {2}, 1);
F_3; g = x_(1,3)*e_(3, {2}, 1);
B = oiGB({f, g, h}, Verbose => true)
C = oiSyz(B, d, Verbose => true)
isOIGB C