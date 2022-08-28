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

    -- Keys
    "ColUpRowUp", "ColUpRowDown", "ColDownRowUp", "ColDownRowDown", "RowUpColUp", "RowUpColDown", "RowDownColUp", "RowDownColDown",

    -- Methods
    "makeOIMap", "getOIMaps", "composeOIMaps",
    "makePolynomialOIAlgebra", "getAlgebraInWidth", "getInducedAlgebraMap",
    "getGenWidths", "getDegShifts", "makeFreeOIModule", "getMonomialOrder", "isZero", "getFreeModuleInWidth", "widthOfElement", "freeOIModuleFromElement", "installBasisElements",

    -- Options
    "VariableOrder",
    "DegreeShifts"
}

scan({
    -- Keys
    targWidth, img,
    baseField, varRows, varSym, varOrder, algebras, maps,
    polyOIAlg, basisSym, genWidths, degShifts, monOrder, modules, Width,
    freeOIMod, ringElement, oiMap, idx, ringElement, basisIndex, basisElements,

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

makePolynomialOIAlgebra = method(TypicalValue => PolynomialOIAlgebra, Options => {VariableOrder => RowUpColUp})
makePolynomialOIAlgebra(Ring, ZZ, Symbol) := opts -> (K, c, x) -> (
    if c < 1 then error("Expected at least 1 row of variables");
    v := opts.VariableOrder;
    if not member(v, {
        ColUpRowUp, ColUpRowDown, ColDownRowUp, ColDownRowDown,
        RowUpColUp, RowUpColDown, RowDownColUp, RowDownColDown
    }) then error("Invalid variable order");

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
    else error("Invalid DegreeShifts option");

    -- TODO: VALIDATE MONOMIAL ORDER

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

-- Should also contain the key-value pairs freeOIMod => FreeOIModule, Width => ZZ and basisElements => List
-- Note: the order of basisElements matters, i.e. basisElements#i should correspond to M_i
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
    retHash.basisElements = flatten for i to #F.genWidths - 1 list
        for oiMap in getOIMaps(F.genWidths#i, n) list makeBasisElement makeBasisIndex(F, oiMap, i + 1);

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
    fmod := getFreeModuleInWidth(F, n);
    for i to #F.genWidths - 1 do
        for oiMap in getOIMaps(F.genWidths#i, n) do (
            b := makeBasisElement makeBasisIndex(F, oiMap, i + 1);
            pos := position(fmod.basisElements, elt -> elt === b);

            if pos === null then error("The basis element "|net b|" does not exist in "|net fmod);
            F.basisSym_(oiMap.targWidth, oiMap.img, i + 1) <- fmod_pos
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
        if not idxf === idxg then if idxf < idxg then return symbol > else return symbol <;
        if not oiMapf.targWidth === oiMapg.targWidth then return oiMapf.targWidth ? oiMapg.targWidth;
        if not oiMapf.img === oiMapg.img then return oiMapf.img ? oiMapg.img;

        use class eltf; -- Note: since oiMapf.targWidth = oiMapg.targWidth we have class eltf === class eltg
        return eltf ? eltg
    )
    else if instance(monOrder, List) then ( -- SCHREYER ORDER
        -- TODO: Implement this
    )
    else error "Monomial order not supported"
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
    if isZero f then error("getOITermsFromVector expects a nonzero input");
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
        pos := position(freeMod.basisElements, elt -> elt === basisElement);
        vect = vect + ringElement * freeMod_pos
    );
    
    vect
)

leadOITerm = method(TypicalValue => OITerm)
leadOITerm VectorInWidth := f -> (
    if isZero f then return null;
    oiTerms := getOITermsFromVector f;
    oiTerms#0
)

leadTerm VectorInWidth := f -> (
    if isZero f then return null;
    loitf := leadOITerm f;
    getVectorFromOITerms {loitf}
)

leadCoefficient VectorInWidth := f -> (
    if isZero f then return null;
    loitf := leadOITerm f;
    leadCoefficient loitf.ringElement
)

leadMonomial VectorInWidth := f -> (
    if isZero f then return null;
    loitf := leadOITerm f;
    getVectorFromOITerms {makeOITerm(loitf.ringElement // leadCoefficient loitf.ringElement, loitf.basisIndex)}
)

-- Scale a VectorInWidth by a number
VectorInWidth // Number := (f, r) -> (
    if isZero f then return f;
    freeOIMod := freeOIModuleFromElement f;
    oiTerms := getOITermsFromVector f;
    getVectorFromOITerms for oiTerm in oiTerms list makeOITerm(oiTerm.ringElement // r_(class oiTerm.ringElement), oiTerm.basisIndex)
)

--oiTermDiv = method(TypicalValue => HashTable)
-- TODO: Implement this

lcm(OITerm, OITerm) := (f, g) -> (
    if not f.basisIndex === g.basisIndex then return makeOITerm(0_(class f.ringElement), f.basisIndex);

    makeOITerm(lcm(f.ringElement // leadCoefficient f.ringElement, g.ringElement // leadCoefficient g.ringElement), f.basisIndex)
)

lcm(VectorInWidth, VectorInWidth) := (f, g) -> getVectorFromOITerms {lcm(leadOITerm f, leadOITerm g)}

terms VectorInWidth := f -> (
    oiTerms := getOITermsFromVector f;
    for oiTerm in oiTerms list getVectorFromOITerms {oiTerm}
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
F = makeFreeOIModule(P, e, {1})
installBasisElements(F, 2)