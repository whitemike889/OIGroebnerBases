--------------------------------------------------------------------------------
-- FROM: FreeOIModules.m2 ------------------------------------------------------
--------------------------------------------------------------------------------

-- Define the new type FreeOIModule
-- COMMENT: The lengths of genWidths and degShifts need to be the same
FreeOIModule = new Type of HashTable
net FreeOIModule := F -> (
    "Polynomial OI-Algebra: "|net(toString(F#"alg")) ||
    "Basis symbol: "|net(toString(F#"basisSym")) ||
    "Generator widths: "|net(toString(F#"genWidths")) ||
    "Degree shifts: "|net(toString(F#"degShifts"))
)

-- PURPOSE: Check if a given FreeOIModule object is valid
-- INPUT: A FreeOIModule 'F'
-- OUTPUT: Nothing if F is a valid FreeOIModule object, otherwise error
validateFreeOIModule = method()
validateFreeOIModule FreeOIModule := F -> (
    if not sort keys F == sort {"alg", "basisSym", "genWidths", "degShifts", "modules", "maps"} or not (instance(F#"modules", MutableHashTable) and instance(F#"maps", MutableHashTable)) then error "Invalid FreeOIModule HashTable keys";
    if not instance(F#"alg", PolynomialOIAlgebra) then error("Expected PolynomialOIAlgebra, not "|toString(F#"alg"));
    validatePolynomialOIAlgebra(F#"alg");

    if not instance(F#"basisSym", Symbol) then error("Expected basis symbol, not "|toString(F#"basisSym"));

    if not instance(F#"genWidths", List) then error("Expected type List for genWidths, not "|toString(class(F#"genWidths")));
    for l in F#"genWidths" do if not instance(l, ZZ) then error("Expected a list of integers for genWidths, not "|toString(F#"genWidths"));

    if not instance(F#"degShifts", List) then error("Expected type List for degShifts, not "|toString(class(F#"degShifts")));
    for l in F#"degShifts" do if not instance(l, ZZ) then error("Expected a list of integers for degShifts, not "|toString(F#"degShifts"));

    if not #(F#"genWidths") == #(F#"degShifts") then error "Length of genWidths must equal length of degShifts";
)

-- PURPOSE: Make a new FreeOIModule
-- INPUT: '(P, e, W)', a PolynomialOIAlgebra 'P', a basis symbol 'e' and a list of generator widths 'W'
-- OUTPUT: A FreeOIModule made from P, e, W
-- COMMENT: Default degree shifts are all zero
freeOIModule = method(TypicalValue => FreeOIModule, Options => {"shifts" => 0})
freeOIModule(PolynomialOIAlgebra, Symbol, List) := opts -> (P, e, W) -> (
    shifts := new MutableList;
    if opts#"shifts" === 0 then for i to #W - 1 do shifts#i = 0
    else if instance(opts#"shifts", List) then for i to #(opts#"shifts") - 1 do shifts#i = (opts#"shifts")#i
    else error("Invalid shifts option: "|toString(opts#"shifts"));

    ret := new FreeOIModule from {"alg" => P, "basisSym" => e, "genWidths" => W, "degShifts" => toList(shifts), "modules" => new MutableHashTable, "maps" => new MutableHashTable};
    validateFreeOIModule ret;

    ret
)

-- PURPOSE: Get the free module from a FreeOIModule in a specified width
-- INPUT: '(F, n)', a FreeOIModule 'F' and a width 'n'
-- OUTPUT: F_n, the free module in width n
-- COMMENT: "store => false" will not store the module in memory (useful for large computations)
getFreeModuleInWidth = method(TypicalValue => Module, Options => {"store" => true})
getFreeModuleInWidth(FreeOIModule, ZZ) := opts -> (F, n) -> (
    validateFreeOIModule F; validateWidth n;
    if not instance(opts#"store", Boolean) then error("Expected \"store\" => true or \"store\" => false, not \"store\" => "|toString(opts#"store"));

    -- Return the module if it already exists
    if (F#"modules")#?n then return (F#"modules")#n;

    local ret;
    alg := getAlgebraInWidth(F#"alg", n, "store" => opts#"store");
    if n == 0 then ret = alg^(#select(F#"genWidths", i -> i == 0))
    else (
        -- Generate the degrees
        degList := new List;
        for i to #(F#"genWidths") - 1 do degList = append(degList, binomial(n, (F#"genWidths")#i) : (F#"degShifts")#i);

        -- Make the module
        ret = alg^degList
    );

    -- Store the module
    if opts#"store" then (F#"modules")#n = ret;

    -- Update the basis elements (compatible with the local lex order)
    basisList := new List;
    for i from 1 to #(F#"genWidths") do (
        oiMaps := reverse(sort(getOIMaps((F#"genWidths")#(i - 1), n)));

        for oiMap in oiMaps do basisList = append(basisList, (F#"basisSym")_(n, toList(oiMap), i));
    );
    if not #basisList == 0 then for i to #basisList - 1 do basisList#i <- ret_i;

    ret
)