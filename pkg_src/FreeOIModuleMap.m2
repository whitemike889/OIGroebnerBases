-- Define the new type FreeOIModuleMap
-- COMMENT: Should be of the form {srcMod => FreeOIModule, targMod => FreeOIModule, genImages => List}
-- COMMENT: genImages should be a list of the images of the generators of srcMod
-- COMMENT: The order of genImages matters, i.e. the width of genImages#i should equal srcMod.genWidths#i
-- COMMENT: To be a graded map, genImages should consist of homogeneous elements and degree(genImages#i) should equal -srcMod.degShifts#i
FreeOIModuleMap = new Type of HashTable
FreeOIModuleMap.synonym = "free OI-module map"

toString FreeOIModuleMap := f -> "source module => "|toString f.srcMod|", target module => "|toString f.targMod|", generator images => "|net f.genImages

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

-- Install juxtaposition method for FreeOIModuleMap and List
-- COMMENT: Applies a FreeOIModuleMap to a List of OITerms and returns the resulting VectorInWidth
FreeOIModuleMap List := (f, oiTerms) -> (
    if #oiTerms == 0 then error "Cannot apply FreeOIModuleMap to an empty list";

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
    ret := newTerms#0;
    for i from 1 to #newTerms - 1 do ret = ret + newTerms#i;
    ret
)

-- Install juxtaposition method for FreeOIModuleMap and List
-- COMMENT: Applies a FreeOIModuleMap to the List of OITerms obtained from a VectorInWidth
FreeOIModuleMap VectorInWidth := (f, v) -> (
    freeOIMod := freeOIModuleFromElement v;
    if not source f === freeOIMod then error "Element "|net v|" does not belong to source of "|toString f;

    oiTerms := getOITermsFromVector v;
    f oiTerms
)

-- Check if a FreeOIModuleMap is a graded map
isHomogeneous FreeOIModuleMap := f -> (
    for elt in f.genImages do if not isHomogeneous elt then return false;
    -f.srcMod.degShifts == flatten apply(f.genImages, degree)
)