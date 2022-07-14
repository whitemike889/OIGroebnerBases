-- Define the new type FreeOIModuleMap
-- COMMENT: Should be of the form {srcMod => FreeOIModule, targMod => FreeOIModule, genImages => List}
-- COMMENT: genImages should be a list of the images of the generators of srcMod
-- COMMENT: The order of genImages matters, i.e. the width of genImages#i should equal srcMod.genWidths#i
-- COMMENT: To be a graded map, genImages should consist of homogeneous elements and degree(genImages#i) should equal -srcMod.degShifts#i
FreeOIModuleMap = new Type of HashTable

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

-- PURPOSE: Check if a FreeOIModuleMap is zero
-- INPUT: A FreeOIModuleMap 'f'
-- OUTPUT: true if f is the zero map, false otherwise
isZero FreeOIModuleMap := f -> isZero f.srcMod or isZero f.targMod

-- PURPOSE: Apply a FreeOIModuleMap to a List of OITerms
-- INPUT: '(f, oiTerms)', a FreeOIModuleMap 'f' and a List of OITerms 'oiTerms'
-- OUTPUT: The VectorInWidth f(oiTerms)
fommToOITerms = method(TypicalValue => VectorInWidth)
fommToOITerms(FreeOIModuleMap, List) := (f, oiTerms) -> (
    if #oiTerms == 0 then error "Cannot apply FreeOIModuleMap to an empty list";

    -- Handle the zero map case
    if isZero f then (
        Width := (oiTerms#0).basisIndex.oiMap.Width;
        return 0_(getFreeModuleInWidth(f.targMod, Width))
    );

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
    sum toList newTerms
)

-- Install juxtaposition method for FreeOIModuleMap and List
-- COMMENT: Applies a FreeOIModuleMap to a List of VectorInWidths
FreeOIModuleMap List := (f, L) -> for i to #L - 1 list f L#i

-- Install juxtaposition method for FreeOIModuleMap and List
-- COMMENT: Applies a FreeOIModuleMap to the List of OITerms obtained from a VectorInWidth
FreeOIModuleMap VectorInWidth := (f, v) -> (
    freeOIMod := freeOIModuleFromElement v;
    if not source f === freeOIMod then error "Element "|net v|" does not belong to source of "|toString f;

    -- Handle the zero map and zero vector cases
    if isZero f or isZero v then (
        Width := widthOfElement v;
        return 0_(getFreeModuleInWidth(f.targMod, Width))
    );

    oiTerms := getOITermsFromVector v;
    fommToOITerms(f, oiTerms)
)

-- Check if a FreeOIModuleMap is a graded map
isHomogeneous FreeOIModuleMap := f -> (
    if isZero f then return true;

    for elt in f.genImages do (
        degs := for t in terms elt list degree t;
        if not #(set degs) == 1 then return false
    );

    -f.srcMod.degShifts == flatten apply(f.genImages, degree)
)