--------------------------------------------------------------------------------
-- BEGIN: InducedModuleMap.m2 --------------------------------------------------
--------------------------------------------------------------------------------

-- Define the new type InducedModuleMap
-- COMMENT: Should be of the form {freeOIMod => FreeOIModule, oiMap => OIMap, assignment => HashTable}
-- COMMENT: assignment should specify how a BasisIndex in the source free module gets mapped to a basis index in the target free module
InducedModuleMap = new Type of HashTable
InducedModuleMap.synonym = "induced module map"

net InducedModuleMap := f -> "Source module: "|net source f ||
    "Target module: "|net target f ||
    "OI-map: "|toString f.oiMap ||
    "Assignment: "|net f.assignment

source InducedModuleMap := f -> getFreeModuleInWidth(f.freeOIMod, #f.oiMap.assignment)
target InducedModuleMap := f -> getFreeModuleInWidth(f.freeOIMod, f.oiMap.Width)

-- PURPOSE: Get the module map induced by an OI-map
-- INPUT: '(F, f)', a FreeOIModule 'F' and an OIMap 'f'
-- OUTPUT: The map F(f)
getInducedModuleMap = method(TypicalValue => InducedModuleMap)
getInducedModuleMap(FreeOIModule, OIMap) := (F, f) -> (
    -- Return the map if it already exists
    if F.maps#?(f.Width, f.assignment) then return F.maps#(f.Width, f.assignment);

    -- Generate the assignment
    m := #f.assignment;
    n := f.Width;
    fmodm := getFreeModuleInWidth(F, m);
    fmodn := getFreeModuleInWidth(F, n);
    basisElementsm := fmodm.basisElements;
    basisElementsn := fmodn.basisElements;
    mutableAssignment := new MutableHashTable;
    for basisElementm in basisElementsm do (
        newBasisIndex := makeBasisIndex(F, composeOIMaps(f, basisElementm.basisIndex.oiMap), basisElementm.basisIndex.idx);
        mutableAssignment#(basisElementm.basisIndex) = newBasisIndex
    );

    -- Make the map
    ret := new InducedModuleMap from {freeOIMod => F, oiMap => f, assignment => new HashTable from mutableAssignment};

    -- Store the map
    F.maps#(f.Width, f.assignment) = ret;

    ret
)

-- PURPOSE: Get the induced module maps between two widths
-- INPUT: '(F, m, n)', a FreeOIModule 'F', a width 'm' and a width 'n'
-- OUTPUT: A List of the elements in F(Hom(m,n))
getInducedModuleMaps = method(TypicalValue => List)
getInducedModuleMaps(FreeOIModule, ZZ, ZZ) := (F, m, n) -> (
    oiMaps := getOIMaps(m, n);
    ret := new List;
    for oiMap in oiMaps do ret = append(ret, getInducedModuleMap(F, oiMap));
    ret
)

-- Install juxtaposition method for InducedModuleMap and List
-- COMMENT: Applies an InducedModuleMap to a List of OITerms and returns the resulting VectorInWidth
InducedModuleMap List := (f, oiTerms) -> (
    if #oiTerms == 0 then error "Cannot apply InducedModuleMap to an empty list";

    -- Generate the new terms
    algMap := getInducedAlgebraMap(f.freeOIMod.polyOIAlg, f.oiMap);
    newTerms := new List;
    for oiTerm in  oiTerms do (
        ringElement := oiTerm.ringElement;
        basisIndex := oiTerm.basisIndex;
        newRingElement := algMap ringElement;
        newBasisIndex := f.assignment#basisIndex;
        newTerms = append(newTerms, makeOITerm(newRingElement, newBasisIndex))
    );
    
    getVectorFromOITerms newTerms
)

-- Install juxtaposition method for InducedModuleMap and VectorInWidth
InducedModuleMap VectorInWidth := (f, v) -> (
    freeOIMod := f.freeOIMod;
    freeOIModFromVector := freeOIModuleFromElement v;
    if not freeOIMod === freeOIModFromVector then error "Incompatible free OI-modules";
    if not source f === class v then error "Element "|net v|" does not belong to source of "|toString f;

    f getOITermsFromVector v
)

--------------------------------------------------------------------------------
-- END: InducedModuleMap.m2 ----------------------------------------------------
--------------------------------------------------------------------------------