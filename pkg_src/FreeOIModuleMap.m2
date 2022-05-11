--------------------------------------------------------------------------------
-- BEGIN: FreeOIModuleMap.m2 ---------------------------------------------------
--------------------------------------------------------------------------------

-- Define the new type FreeOIModuleMap
-- COMMENT: Should be of the form {srcMod => FreeOIModule, targMod => FreeOIModule, targElements => List}
FreeOIModuleMap = new Type of HashTable
FreeOIModuleMap.synonym = "free OI-module map"

-- Install net method for FreeOIModuleMap
net FreeOIModuleMap := f -> "Source module: "|toString f.srcMod ||
    "Target module: "|toString f.targMod ||
    "Target elements: "|toString f.targElements

-- PURPOSE: Make a new FreeOIModuleMap
-- INPUT: '(G, F, L)', a target FreeOIModule 'G', a source FreeOIModule 'F' and a List 'L' of elements of G
-- OUTPUT: A FreeOIModuleMap made from G, F and L
makeFreeOIModuleMap = method(TypicalValue => FreeOIModuleMap, Options => {VerifyData => true})
makeFreeOIModuleMap(FreeOIModule, FreeOIModule, List) := opts -> (G, F, L) -> (
    ret := new FreeOIModuleMap from {srcMod => F, targMod => G, targElements => L};
    if opts.VerifyData then verifyData ret;
    ret
)

-- Verifcation method for FreeOIModuleMap
verifyData FreeOIModuleMap := f -> (
    if not sort keys f === sort {srcMod, targMod, targElements} then error("Expected keys {srcMod, targMod, targElements}, instead got "|toString keys f);
    if not instance(f.srcMod, FreeOIModule) or not instance(f.targMod, FreeOIModule) then error("Expected type FreeOIModule for srcMod and targMod, instead got types "|toString class f.srcMod|" and "|toString class f.targMod);
    if f.srcMod === f.targMod then error "srcMod cannot equal targMod";
    scan({f.srcMod, f.targMod}, verifyData);
    
    if not instance(f.targElements, List) or #f.targElements == 0 then error("Expected nonempty List for targElements, instead got "|toString f.targElements);
    for i to #f.targElements - 1 do (
        elt := f.targElements#i;
        if not instance(elt, Vector) then error("Expected a Vector, instead got "|toString elt);
        verifyData elt;
        
        if not (class elt).Width == f.srcMod.genWidths#i then error("Element "|toString i|" of targElements has width "|toString (class elt).Width|" which does not match srcMod.genWidths#"|toString i|" = "|toString f.srcMod.genWidths#i)
    )
)

--------------------------------------------------------------------------------
-- END: FreeOIModuleMap.m2 -----------------------------------------------------
--------------------------------------------------------------------------------