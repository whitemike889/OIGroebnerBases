--------------------------------------------------------------------------------
-- BEGIN: FreeOIModuleMap.m2 ---------------------------------------------------
--------------------------------------------------------------------------------

-- Define the new type FreeOIModuleMap
-- COMMENT: Should be of the form {srcMod => FreeOIModule, targMod => FreeOIModule, basisImage => List}
FreeOIModuleMap = new Type of HashTable
FreeOIModuleMap.synonym = "free OI-module map"

toString FreeOIModuleMap := f -> "source module => "|toString f.srcMod|", target module => "|toString f.targMod|", basis image => "|toString f.basisImage

net FreeOIModuleMap := f -> "Source module: "|toString f.srcMod ||
    "Target module: "|toString f.targMod ||
    "Basis image: "|toString f.basisImage

source FreeOIModuleMap := f -> f.srcMod
target FreeOIModuleMap := f -> f.targMod

-- PURPOSE: Make a new FreeOIModuleMap
-- INPUT: '(G, F, L)', a target FreeOIModule 'G', a source FreeOIModule 'F' and a List 'L' of elements of G
-- OUTPUT: A FreeOIModuleMap made from G, F and L
makeFreeOIModuleMap = method(TypicalValue => FreeOIModuleMap)
makeFreeOIModuleMap(FreeOIModule, FreeOIModule, List) := (G, F, L) -> new FreeOIModuleMap from {srcMod => F, targMod => G, basisImage => L}

--------------------------------------------------------------------------------
-- END: FreeOIModuleMap.m2 -----------------------------------------------------
--------------------------------------------------------------------------------