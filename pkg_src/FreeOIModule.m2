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

load "SchreyerMonomialOrder.m2" -- Must be loaded after FreeOIModule is declared

-- Validation method for FreeOIModule
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

    ret := new FreeOIModule from {
        oiAlgebra => P,
        basisSym => e,
        genWidths => W,
        degShifts => toList shifts,
        monOrder => new MutableList from {Lex},
        modules => new MutableHashTable,
        maps => new MutableHashTable};
    assertValid ret;

    ret
)

load "OIMonomial.m2"

-- PURPOSE: Get the free module from a FreeOIModule in a specified width
-- INPUT: '(F, n)', a FreeOIModule 'F' and a width 'n'
-- OUTPUT: F_n, the free module in width n
-- COMMENT: "Store => false" will not store the module in memory (useful for large computations)
-- COMMENT: "UpdateBasis => false" will not modify the basis elements
getFreeModuleInWidth = method(TypicalValue => Module, Options => {Store => true, UpdateBasis => true})
getFreeModuleInWidth(FreeOIModule, ZZ) := opts -> (F, n) -> (
    scan({F, n}, assertValid);
    if not instance(opts.Store, Boolean) then error("Expected boolean value for Store option, instead got "|toString opts.Store);
    if not instance(opts.UpdateBasis, Boolean) then error("Expected boolean value for UpdateBasis option, instead got "|toString opts.UpdateBasis);

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
    if not c.?parentModule then error("Element "|toString f|" has no key parentModule");
    if not instance(c.parentModule, FreeOIModule) then error("Expected FreeOIModule, instead got "|toString c.parentModule);
    c.parentModule
)

--------------------------------------------------------------------------------
-- END: FreeOIModule.m2 --------------------------------------------------------
--------------------------------------------------------------------------------