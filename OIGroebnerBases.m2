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
    "FreeOIModule", "ModuleInWidth", "VectorInWidth",
    "InducedModuleMap",
    "FreeOIModuleMap",

    -- Keys
    "ColUpRowUp", "ColUpRowDown", "ColDownRowUp", "ColDownRowDown", "RowUpColUp", "RowUpColDown", "RowDownColUp", "RowDownColDown",

    -- Methods
    "makeOIMap", "getOIMaps", "composeOIMaps",
    "makePolynomialOIAlgebra", "getAlgebraInWidth", "getInducedAlgebraMap",
    "getGenWidths", "getDegShifts", "makeFreeOIModule", "getMonomialOrder", "isZero", "getFreeModuleInWidth", "widthOfElement", "freeOIModuleFromElement", "installBasisElements",
    "makeMonic",
    "getInducedModuleMap",
    "makeFreeOIModuleMap",

    -- Options
    "VariableOrder",
    "DegreeShifts"
}

scan({
    -- Keys
    targWidth, img,
    baseField, varRows, varSym, varOrder, algebras, maps,
    polyOIAlg, basisSym, genWidths, degShifts, monOrder, modules, Width, basisElements, basisElementPositions,
    freeOIMod, ringElement, oiMap, idx, basisIndex, quo,
    srcMod, targMod, genImages,

    -- Options
    CombineLikeTerms
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
    if not source f === target g then error "maps cannot be composed due to incompatible source and target";
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

makePolynomialOIAlgebra = method(TypicalValue => PolynomialOIAlgebra, Options => {VariableOrder => RowUpColUp})
makePolynomialOIAlgebra(Ring, ZZ, Symbol) := opts -> (K, c, x) -> (
    if c < 1 then error "expected at least one row of variables";
    v := opts.VariableOrder;
    if not member(v, {
        ColUpRowUp, ColUpRowDown, ColDownRowUp, ColDownRowDown,
        RowUpColUp, RowUpColDown, RowDownColUp, RowDownColDown
    }) then error "invalid variable order";

    new PolynomialOIAlgebra from {
            baseField => K,
            varRows => c,
            varSym => x,
            varOrder => v,
            algebras => new MutableHashTable,
            maps => new MutableHashTable}
)

-- Lookup table for linearFromRowCol
orderTable := new HashTable from {
    ColUpRowUp => (P, n, i, j) -> P.varRows * (n - j + 1) - i,
    ColUpRowDown => (P, n, i, j) -> P.varRows * (n - j) + i - 1,
    ColDownRowUp => (P, n, i, j) -> P.varRows * j - i,
    ColDownRowDown => (P, n, i, j) -> P.varRows * (j - 1) + i - 1,
    RowUpColUp => (P, n, i, j) -> n * (P.varRows - i + 1) - j,
    RowUpColDown => (P, n, i, j) -> n * (P.varRows - i) + j - 1,
    RowDownColUp => (P, n, i, j) -> n * i - j,
    RowDownColDown => (P, n, i, j) -> n * (i - 1) + j - 1
}

-- Linearize the variables based on P.varOrder
linearFromRowCol := (P, n, i, j) -> (orderTable#(P.varOrder))(P, n, i, j)

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

-- Should be of the form {polyOIAlg => PolynomialOIAlgebra, basisSym => Symbol, genWidths => List, degShifts => List, monOrder => Thing, modules => MutableHashTable, maps => MutableHashTable}
FreeOIModule = new Type of HashTable

toString FreeOIModule := F -> "("|toString F.basisSym|", "|toString F.genWidths|", "|toString F.degShifts|")"

net FreeOIModule := F -> (
    local monOrderNet;
    if F.monOrder === Lex then monOrderNet = net Lex
    else if instance(F.monOrder, List) then monOrderNet = "Schreyer order induced by "|net F.monOrder;

    "Polynomial OI-algebra: "|toString F.polyOIAlg ||
    "Basis symbol: "|net F.basisSym ||
    "Generator widths: "|net F.genWidths ||
    "Degree shifts: "|net F.degShifts ||
    "Monomial order: "|monOrderNet
)

getGenWidths = method(TypicalValue => List)
getGenWidths FreeOIModule := F -> F.genWidths

getDegShifts = method(TypicalValue => List)
getDegShifts FreeOIModule := F -> F.degShifts

makeFreeOIModule = method(TypicalValue => FreeOIModule, Options => {DegreeShifts => null, MonomialOrder => Lex})
makeFreeOIModule(PolynomialOIAlgebra, Symbol, List) := opts -> (P, e, W) -> (
    local shifts;
    if opts.DegreeShifts === null then shifts = toList(#W : 0)
    else if instance(opts.DegreeShifts, List) then shifts = opts.DegreeShifts
    else error "invalid DegreeShifts option";

    -- Validate the monomial order
    if not opts.MonomialOrder === Lex and not (
        instance(opts.MonomialOrder, List) and 
        W === apply(opts.MonomialOrder, widthOfElement) and 
        #set apply(opts.MonomialOrder, freeOIModuleFromElement) == 1) then error "invalid monomial order";

    new FreeOIModule from {
        polyOIAlg => P,
        basisSym => e,
        genWidths => W,
        degShifts => shifts,
        monOrder => opts.MonomialOrder,
        modules => new MutableHashTable,
        maps => new MutableHashTable}
)

getMonomialOrder = method()
getMonomialOrder FreeOIModule := F -> F.monOrder

-- Should also contain the key-value pairs freeOIMod => FreeOIModule, Width => ZZ, basisElements => List, and basisElementPositions => HashTable
ModuleInWidth = new Type of Module

net ModuleInWidth := M -> (
    rawMod := new Module from M;
    net rawMod | " in width " | net rawMod.Width
)

-- Each element 'f' in a ModuleInWidth 'M' should have type VectorInWidth with class f === M
VectorInWidth = new Type of Vector

isZero = method(TypicalValue => Boolean)
isZero VectorInWidth := f -> f === 0_(class f)
isZero FreeOIModule := F -> #F.genWidths === 0

net VectorInWidth := f -> (
    if isZero f then return net 0;
    oiTerms := getOITermsFromVector(f, CombineLikeTerms => true);
    if #oiTerms == 1 then return net oiTerms#0;
    
    str := "";
    for i to #oiTerms - 2 do str = str|net oiTerms#i|" + "; -- TODO: Make negatives look better
    str = str|net oiTerms#-1;
    str
)

getFreeModuleInWidth = method(TypicalValue => ModuleInWidth)
getFreeModuleInWidth(FreeOIModule, ZZ) := (F, n) -> (
    -- Return the module if it already exists
    if F.modules#?n then ( use ring F.modules#n; return F.modules#n );

    -- Generate the degrees
    alg := getAlgebraInWidth(F.polyOIAlg, n);
    degList := for i to #F.genWidths - 1 list binomial(n, F.genWidths#i) : F.degShifts#i;

    -- Make the module
    retHash := new MutableHashTable from alg^degList;
    retHash.Width = n;
    retHash.freeOIMod = F;
    
    -- Generate the basis elements
    k := 0;
    mutPos := new MutableHashTable;
    retHash.basisElements = flatten for i to #F.genWidths - 1 list
        for oiMap in getOIMaps(F.genWidths#i, n) list (
            b := makeBasisElement makeBasisIndex(F, oiMap, i + 1);
            mutPos#b = k;
            k = k + 1;
            b
        );
    
    retHash.basisElementPositions = new HashTable from mutPos;

    ret := new ModuleInWidth of VectorInWidth from retHash;

    -- Store the module
    F.modules#n = ret;

    ret
)

-- Shorthand for getFreeModuleInWidth
FreeOIModule _ ZZ := (F, n) -> getFreeModuleInWidth(F, n)

widthOfElement = method(TypicalValue => ZZ)
widthOfElement VectorInWidth := f -> (class f).Width

freeOIModuleFromElement = method(TypicalValue => FreeOIModule)
freeOIModuleFromElement VectorInWidth := f -> (class f).freeOIMod

installBasisElements = method()
installBasisElements(FreeOIModule, ZZ) := (F, n) -> (
    freeMod := getFreeModuleInWidth(F, n);
    for i to #F.genWidths - 1 do
        for oiMap in getOIMaps(F.genWidths#i, n) do (
            b := makeBasisElement makeBasisIndex(F, oiMap, i + 1);
            F.basisSym_(oiMap.targWidth, oiMap.img, i + 1) <- freeMod_(freeMod.basisElementPositions#b)
        )
)

-- Should be of the form {freeOIMod => FreeOIModule, oiMap => OIMap, idx => ZZ}
BasisIndex = new Type of HashTable

makeBasisIndex = method(TypicalValue => BasisIndex)
makeBasisIndex(FreeOIModule, OIMap, ZZ) := (F, f, i) -> new BasisIndex from {freeOIMod => F, oiMap => f, idx => i}

-- Should be of the form {ringElement => RingElement, basisIndex => BasisIndex}
OITerm = new Type of HashTable

makeOITerm = method(TypicalValue => OITerm)
makeOITerm(RingElement, BasisIndex) := (elt, b) -> new OITerm from {ringElement => elt, basisIndex => b}

net OITerm := f -> (
    local ringElementNet;
    if #terms f.ringElement == 1 or #terms f.ringElement == 0 then ringElementNet = net f.ringElement
    else ringElementNet = "("|net f.ringElement|")";
    ringElementNet | net f.basisIndex.freeOIMod.basisSym_(toString f.basisIndex.oiMap.targWidth, toString f.basisIndex.oiMap.img, f.basisIndex.idx)
)

isZero OITerm := f -> f.ringElement === 0_(class f.ringElement)
isZero RingElement := f -> f === 0_(class f)

-- Cache for storing OITerm comparisons
oiTermCompCache = new MutableHashTable

-- Comparison method for OITerm
OITerm ? OITerm := (f, g) -> (
    -- Return the comparison if it already exists
    if oiTermCompCache#?(f, g) then return oiTermCompCache#(f, g);

    local ret;

    -- Generate the comparison
    if f === g or (isZero f and isZero g) then ret = symbol == 
    else if isZero f then ret = symbol < else if isZero g then ret = symbol > else (
        eltf := f.ringElement; eltg := g.ringElement;
        bf := f.basisIndex; bg := g.basisIndex;
        oiMapf := bf.oiMap; oiMapg := bg.oiMap;
        idxf := bf.idx; idxg := bg.idx;

        if not bf.freeOIMod === bg.freeOIMod then ret = incomparable else (
            freeOIMod := bf.freeOIMod;

            monOrder := getMonomialOrder freeOIMod;
            if monOrder === Lex then ( -- LEX ORDER
                if not idxf === idxg then ( if idxf < idxg then ret = symbol > else ret = symbol < )
                else if not oiMapf.targWidth === oiMapg.targWidth then ret = oiMapf.targWidth ? oiMapg.targWidth
                else if not oiMapf.img === oiMapg.img then ret = oiMapf.img ? oiMapg.img
                else ret = eltf ? eltg
            )
            else if instance(monOrder, List) then ( -- SCHREYER ORDER
                freeOIModMap := makeFreeOIModuleMap(freeOIModuleFromElement monOrder#0, freeOIMod, monOrder);
                imgf := applyFreeOIModuleMap(freeOIModMap, {f});
                imgg := applyFreeOIModuleMap(freeOIModMap, {g});
                loimimf := makeMonic leadOITerm imgf;
                loimimg := makeMonic leadOITerm imgg;

                if not loimimf === loimimg then ret = loimimf ? loimimg
                else if not idxf === idxg then ( if idxf < idxg then ret = symbol > else ret = symbol < )
                else if not oiMapf.targWidth === oiMapg.targWidth then ret = oiMapf.targWidth ? oiMapg.targWidth
                else if not oiMapf.img === oiMapg.img then ret = oiMapf.img ? oiMapg.img
                else ret = symbol ==
            )
            else error "monomial order not supported"
        )
    );

    -- Store the comparison
    oiTermCompCache#(f, g) = ret;

    ret
)

-- Comparison method for VectorInWidth
VectorInWidth ? VectorInWidth := (f, g) -> leadOITerm f ? leadOITerm g

makeBasisElement = method(TypicalValue => OITerm)
makeBasisElement BasisIndex := b -> (
    one := 1_(getAlgebraInWidth(b.freeOIMod.polyOIAlg, b.oiMap.targWidth));
    new OITerm from {ringElement => one, basisIndex => b}
)

getOITermsFromVector = method(TypicalValue => List, Options => {CombineLikeTerms => false})
getOITermsFromVector VectorInWidth := opts -> f -> (
    if isZero f then error "the zero element has no OI-terms";
    freeMod := class f;
    entryList := entries f;

    if opts.CombineLikeTerms then reverse sort for i to #entryList - 1 list (
        if isZero entryList#i then continue;
        makeOITerm(entryList#i, (freeMod.basisElements#i).basisIndex)
    ) else reverse sort flatten for i to #entryList - 1 list (
        if isZero entryList#i then continue;
        for term in terms entryList#i list makeOITerm(term, (freeMod.basisElements#i).basisIndex)
    )
)

getVectorFromOITerms = method(TypicalValue => VectorInWidth)
getVectorFromOITerms List := L -> (
    if #L == 0 then error("getVectorFromOITerms expects a nonempty input");
    Width := (L#0).basisIndex.oiMap.targWidth;
    freeOIMod := (L#0).basisIndex.freeOIMod;
    freeMod := getFreeModuleInWidth(freeOIMod, Width);
    vect := 0_freeMod;

    for oiTerm in L do (
        ringElement := oiTerm.ringElement;
        basisElement := makeBasisElement oiTerm.basisIndex;
        vect = vect + ringElement * freeMod_(freeMod.basisElementPositions#basisElement)
    );
    
    vect
)

leadOITerm = method(TypicalValue => OITerm)
leadOITerm VectorInWidth := f -> (
    if isZero f then error "the zero element has no lead OI-term";
    oiTerms := getOITermsFromVector f;
    oiTerms#0
)

leadTerm VectorInWidth := f -> (
    if isZero f then return f;
    loitf := leadOITerm f;
    getVectorFromOITerms {loitf}
)

leadCoefficient VectorInWidth := f -> (
    if isZero f then return 0_((freeOIModuleFromElement f).polyOIAlg.baseField);
    loitf := leadOITerm f;
    leadCoefficient loitf.ringElement
)

leadCoefficient OITerm := f -> leadCoefficient f.ringElement

leadMonomial VectorInWidth := f -> (
    if isZero f then error "the zero element has no lead monomial";
    loitf := leadOITerm f;
    getVectorFromOITerms {makeMonic loitf}
)

-- Scale a VectorInWidth by a number
VectorInWidth // Number := (f, r) -> (
    if isZero f then return f;
    oiTerms := getOITermsFromVector f;
    getVectorFromOITerms for oiTerm in oiTerms list oiTerm // r
)

-- Scale an OITerm by a number
OITerm // Number := (f, r) -> (
    if isZero f then return f;
    makeOITerm(f.ringElement // r_(class f.ringElement), f.basisIndex)
)

makeMonic = method(TypicalValue => VectorInWidth)
makeMonic OITerm := f -> if isZero f then error "cannot make the zero element monic" else f // leadCoefficient f
makeMonic VectorInWidth := f -> if isZero f then error "cannot make the zero element monic" else f // leadCoefficient f

-- Tries to divide f by g
-- Returns a HashTable of the form {quo => RingElement, oiMap => OIMap}
oiTermDiv = method(TypicalValue => HashTable)
oiTermDiv(OITerm, OITerm) := (f, g) -> (
    if isZero g then error "cannot divide an OI-term by zero";
    retZero := new HashTable from {quo => 0_(class f.ringElement), oiMap => null};
    if isZero f then return retZero;

    freeOIModf := f.basisIndex.freeOIMod;
    freeOIModg := g.basisIndex.freeOIMod;
    if not freeOIModf === freeOIModg then return retZero;

    Widthf := f.basisIndex.oiMap.targWidth;
    Widthg := g.basisIndex.oiMap.targWidth;
    if Widthf < Widthg then return retZero;
    if Widthf === Widthg then (
        if not f.basisIndex === g.basisIndex then return retZero;
        if isZero(f.ringElement % g.ringElement) then return new HashTable from {quo => f.ringElement // g.ringElement, oiMap => (getOIMaps(Widthg, Widthf))#0} else return retZero
    );

    oiMaps := getOIMaps(Widthg, Widthf);
    for oiMap in oiMaps do (
        modMap := getInducedModuleMap(freeOIModf, oiMap);
        img := leadOITerm applyModuleMap(modMap, {g});
        if not img.basisIndex === f.basisIndex then continue;
        if isZero(f.ringElement % img.ringElement) then return new HashTable from {quo => f.ringElement // img.ringElement, oiMap => oiMap}
    );

    retZero
)

-- Divide the lead terms of two VectorInWidths
VectorInWidth // VectorInWidth := (f, g) -> if isZero f then return f else if isZero g then error "cannot divide by zero" else values oiTermDiv(leadOITerm f, leadOITerm g)

lcm(OITerm, OITerm) := (f, g) -> (
    if not f.basisIndex === g.basisIndex then return makeOITerm(0_(class f.ringElement), f.basisIndex);

    makeOITerm(lcm(f.ringElement, g.ringElement), f.basisIndex)
)

lcm(VectorInWidth, VectorInWidth) := (f, g) -> if isZero f then f else if isZero g then g else getVectorFromOITerms {lcm(leadOITerm f, leadOITerm g)}

terms VectorInWidth := f -> (
    if isZero f then return {};
    oiTerms := getOITermsFromVector f;
    for oiTerm in oiTerms list getVectorFromOITerms {oiTerm}
)

-- Should be of the form {freeOIMod => FreeOIModule, oiMap => OIMap, img => HashTable}
InducedModuleMap = new Type of HashTable

net InducedModuleMap := f -> "Module map from "|net getFreeModuleInWidth(f.freeOIMod, #f.oiMap.img)|" to "|net getFreeModuleInWidth(f.freeOIMod, f.oiMap.targWidth)|" induced by the OI-map: "|net f.oiMap

source InducedModuleMap := f -> getFreeModuleInWidth(f.freeOIMod, #f.oiMap.img)
target InducedModuleMap := f -> getFreeModuleInWidth(f.freeOIMod, f.oiMap.targWidth)

getInducedModuleMap = method(TypicalValue => InducedModuleMap)
getInducedModuleMap(FreeOIModule, OIMap) := (F, f) -> (
    -- Return the map if it already exists
    if F.maps#?f then return F.maps#f;

    -- Generate the BasisIndex assignments
    m := #f.img;
    freeModm := getFreeModuleInWidth(F, m);
    basisElementsm := freeModm.basisElements;
    indexImages := new HashTable from for basisElementm in basisElementsm list basisElementm.basisIndex => makeBasisIndex(F, composeOIMaps(f, basisElementm.basisIndex.oiMap), basisElementm.basisIndex.idx);

    -- Make the map
    ret := new InducedModuleMap from {freeOIMod => F, oiMap => f, img => indexImages};

    -- Store the map
    F.maps#f = ret;

    ret
)

-- Cache for storing InducedModuleMap images
modMapCache = new MutableHashTable

-- Apply an InducedModuleMap to a List of OI-terms
applyModuleMap = method(TypicalValue => VectorInWidth)
applyModuleMap(InducedModuleMap, List) := (f, oiTerms) -> (
    if #oiTerms == 0 then error "cannot apply InducedModuleMap to an empty list";

    -- Return the image if it already exists
    if modMapCache#?(f, oiTerms) then return modMapCache#(f, oiTerms);

    -- Generate the new terms
    algMap := getInducedAlgebraMap(f.freeOIMod.polyOIAlg, f.oiMap);
    ret := getVectorFromOITerms for oiTerm in oiTerms list (
        ringElement := oiTerm.ringElement;
        basisIndex := oiTerm.basisIndex;
        newRingElement := algMap ringElement;
        newBasisIndex := f.img#basisIndex;
        makeOITerm(newRingElement, newBasisIndex)
    );

    -- Store the image
    modMapCache#(f, oiTerms) = ret;

    ret
)

-- Juxtaposition method for InducedModuleMap and VectorInWidth
InducedModuleMap VectorInWidth := (f, v) -> (
    freeOIMod := f.freeOIMod;
    freeOIModFromVector := freeOIModuleFromElement v;
    if not freeOIMod === freeOIModFromVector then error "element does not belong to the required FreeOIModule";
    if not source f === class v then error "element does not belong to the source of the map";

    -- Handle the zero vector
    if isZero v then (
        targWidth := f.oiMap.targWidth;
        return 0_(getFreeModuleInWidth(freeOIMod, targWidth))
    );

    applyModuleMap(f, getOITermsFromVector v)
)

-- Should be of the form {srcMod => FreeOIModule, targMod => FreeOIModule, genImages => List}
FreeOIModuleMap = new Type of HashTable

net FreeOIModuleMap := f -> "Source module: "|toString f.srcMod ||
    "Target module: "|toString f.targMod ||
    "Generator images: "|net f.genImages

source FreeOIModuleMap := f -> f.srcMod
target FreeOIModuleMap := f -> f.targMod

makeFreeOIModuleMap = method(TypicalValue => FreeOIModuleMap)
makeFreeOIModuleMap(FreeOIModule, FreeOIModule, List) := (G, F, L) -> new FreeOIModuleMap from {srcMod => F, targMod => G, genImages => L}

isZero FreeOIModuleMap := f -> isZero f.srcMod or isZero f.targMod

-- Cache for storing FreeOIModuleMap images
freeOIModMapCache = new MutableHashTable

-- Apply a FreeOIModuleMap to a List of OITerms
applyFreeOIModuleMap = method(TypicalValue => VectorInWidth)
applyFreeOIModuleMap(FreeOIModuleMap, List) := (f, oiTerms) -> (
    if #oiTerms == 0 then error "cannot apply FreeOIModuleMap to an empty list";

    -- Return the image if it already exists
    if freeOIModMapCache#?(f, oiTerms) then return freeOIModMapCache#(f, oiTerms);

    -- Handle the zero map case
    if isZero f then (
        targWidth := (oiTerms#0).basisIndex.oiMap.targWidth;
        return 0_(getFreeModuleInWidth(f.targMod, targWidth))
    );

    -- Generate the new terms
    newTerms := for oiTerm in oiTerms list (
        ringElement := oiTerm.ringElement;
        basisIndex := oiTerm.basisIndex;
        oiMap := basisIndex.oiMap;
        idx := basisIndex.idx;
        modMap := getInducedModuleMap(f.targMod, oiMap);
        ringElement * modMap f.genImages#(idx - 1) -- x*d_(pi,i) ---> x*F(pi)(b_i)
    );

    -- Sum the terms up
    ret := sum newTerms;

    -- Store the image
    freeOIModMapCache#(f, oiTerms) = ret;

    ret
)

-- Apply a FreeOIModuleMap to a List of VectorInWidths
FreeOIModuleMap List := (f, L) -> for i to #L - 1 list f L#i

-- Apply a FreeOIModuleMap to a VectorInWidth
FreeOIModuleMap VectorInWidth := (f, v) -> (
    freeOIMod := freeOIModuleFromElement v;
    if not source f === freeOIMod then error "element does not belong to the required FreeOIModule";

    -- Handle the zero map and zero vector cases
    if isZero f or isZero v then (
        Width := widthOfElement v;
        return 0_(getFreeModuleInWidth(f.targMod, Width))
    );

    oiTerms := getOITermsFromVector v;
    applyFreeOIModuleMap(f, oiTerms)
)

-- Check if a FreeOIModuleMap is a graded map
isHomogeneous FreeOIModuleMap := f -> (
    if isZero f then return true;

    for elt in f.genImages do (
        degs := for t in terms elt list degree t;
        if not #(set degs) == 1 then return false
    );

    -f.srcMod.degShifts === flatten apply(f.genImages, degree)
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
P = makePolynomialOIAlgebra(QQ, 1, x)
F = makeFreeOIModule(P, e, {1,2})
installBasisElements(F, 2)
f = 3*x_(1,2)^2*x_(1,1)*e_(2,{2},1)+x_(1,1)*e_(2,{1},1)
g = x_(1,1)*e_(2,{2},1)+e_(2,{1},1)