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
net FreeOIModule := F -> "Polynomial OI-algebra: "|toString F.polyOIAlg ||
    "Basis symbol: "|net F.basisSym ||
    "Generator widths: "|net F.genWidths ||
    "Degree shifts: "|net F.degShifts ||
    "Monomial order: "|net F.monOrder#0

load "SchreyerMonomialOrder.m2" -- Must be loaded after FreeOIModule is declared

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
    if not (F.monOrder#0 === Lex or instance(F.monOrder#0, SchreyerMonomialOrder)) then error("Expected either Lex or type SchreyerMonomialOrder for monOrder#0, instead got "|toString F.monOrder#0)
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

load "TermsAndMonomials.m2"

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
oldNet = Vector # net -- Thanks to Paul Zinn-Justin for showing me this
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

--------------------------------------------------------------------------------
-- END: FreeOIModule.m2 --------------------------------------------------------
--------------------------------------------------------------------------------