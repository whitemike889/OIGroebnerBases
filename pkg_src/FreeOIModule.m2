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

net ModuleInWidth := M -> (
    rawMod := new Module from M;
    net rawMod | " in width " | net rawMod.Width
)

-- Define the new type VectorInWidth
-- COMMENT: An instance f should have class f === (corresponding ModuleInWidth)
VectorInWidth = new Type of Vector
VectorInWidth.synonym = "vector in a specified width"

-- PURPOSE: Check if a VectorInWidth is zero
-- INPUT: A VectorInWidth 'f'
-- OUTPUT: true if f is zero, false otherwise
isZero = method(TypicalValue => Boolean)
isZero VectorInWidth := f -> (
    freeOIMod := freeOIModuleFromElement f;
    Width := widthOfElement f;
    f === 0_(getFreeModuleInWidth(freeOIMod, Width))
)

load "FreeOIModuleMap.m2"

-- PURPOSE: Install a Schreyer monomial order on a FreeOIModule
-- INPUT: A FreeOIModuleMap 'f'
-- OUTPUT: Sets f.srcMod.monOrder#0 to f
installSchreyerMonomialOrder = method()
installSchreyerMonomialOrder FreeOIModuleMap := f -> f.srcMod.monOrder#0 = f

net VectorInWidth := f -> (
    oiTerms := getCombinedOITermsFromVector f;
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

load "Terms.m2"

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