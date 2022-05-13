--------------------------------------------------------------------------------
-- BEGIN: FreeOIModuleMap.m2 ---------------------------------------------------
--------------------------------------------------------------------------------

-- Define the new type FreeOIModuleMap
-- COMMENT: Should be of the form {srcMod => FreeOIModule, targMod => FreeOIModule, genImage => List}
-- COMMENT: genImage should be a list of the images of the generators of srcMod
-- COMMENT: The order of genImage matters, i.e. genImage#i should correspond to srcMod.genWidths#i
FreeOIModuleMap = new Type of HashTable
FreeOIModuleMap.synonym = "free OI-module map"

toString FreeOIModuleMap := f -> "source module => "|toString f.srcMod|", target module => "|toString f.targMod|", generator image => "|toString f.genImage

net FreeOIModuleMap := f -> "Source module: "|toString f.srcMod ||
    "Target module: "|toString f.targMod ||
    "Generator image: "|toString f.genImage

source FreeOIModuleMap := f -> f.srcMod
target FreeOIModuleMap := f -> f.targMod

-- PURPOSE: Make a new FreeOIModuleMap
-- INPUT: '(G, F, L)', a target FreeOIModule 'G', a source FreeOIModule 'F' and a List 'L' of elements of G
-- OUTPUT: A FreeOIModuleMap made from G, F and L
makeFreeOIModuleMap = method(TypicalValue => FreeOIModuleMap)
makeFreeOIModuleMap(FreeOIModule, FreeOIModule, List) := (G, F, L) -> new FreeOIModuleMap from {srcMod => F, targMod => G, genImage => L}

-- Install juxtaposition method for FreeOIModuleMap
FreeOIModuleMap VectorInWidth := (f, v) -> (
    freeOIMod := freeOIModuleFromElement v;
    if not source f === freeOIMod then error "Element "|net v|" does not belong to source of "|toString f;

    Width := widthOfElement v;
    oiTerms := getOITermsFromVector v;

    if #oiTerms == 0 then return null;

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

--------------------------------------------------------------------------------
-- END: FreeOIModuleMap.m2 -----------------------------------------------------
--------------------------------------------------------------------------------