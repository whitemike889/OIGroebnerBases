-- Define the new type InducedModuleMap
-- COMMENT: Should be of the form {freeOIMod => FreeOIModule, oiMap => OIMap, assignment => HashTable}
-- COMMENT: assignment should specify how a BasisIndex in the source free module gets mapped to a basis index in the target free module
InducedModuleMap = new Type of HashTable

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

-- Install juxtaposition method for InducedModuleMap and List
-- COMMENT: Applies an InducedModuleMap to a List of OITerms and returns the resulting VectorInWidth
InducedModuleMap List := (f, oiTerms) -> (
    if #oiTerms == 0 then error "Cannot apply InducedModuleMap to an empty list";

    -- Generate the new terms
    algMap := getInducedAlgebraMap(f.freeOIMod.polyOIAlg, f.oiMap);
    newTerms := new MutableList;
    for i to #oiTerms - 1 do (
        ringElement := (oiTerms#i).ringElement;
        basisIndex := (oiTerms#i).basisIndex;
        newRingElement := algMap ringElement;
        newBasisIndex := f.assignment#basisIndex;
        newTerms#i = makeOITerm(newRingElement, newBasisIndex)
    );
    
    getVectorFromOITerms toList newTerms
)

-- Install juxtaposition method for InducedModuleMap and VectorInWidth
InducedModuleMap VectorInWidth := (f, v) -> (
    freeOIMod := f.freeOIMod;
    freeOIModFromVector := freeOIModuleFromElement v;
    if not freeOIMod === freeOIModFromVector then error "Incompatible free OI-modules";
    if not source f === class v then error "Element "|net v|" does not belong to source of "|toString f;

    -- Handle the zero vector
    if isZero v then (
        targWidth := f.oiMap.Width;
        return 0_(getFreeModuleInWidth(freeOIMod, targWidth))
    );

    f getOITermsFromVector v
)