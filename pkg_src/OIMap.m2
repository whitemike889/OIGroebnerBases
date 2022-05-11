--------------------------------------------------------------------------------
-- BEGIN: OIMap.m2 -------------------------------------------------------------
--------------------------------------------------------------------------------

-- Verification method for ZZ
verifyData ZZ := n -> if n < 0 then error("Expected a nonnegative integer, instead got "|toString n)

-- PURPOSE: Define the new type OIMap
-- COMMENT: Should be of the form {Width => ZZ, assignment => List}
OIMap = new Type of HashTable
OIMap.synonym = "OI-map"

-- Install net method for OIMap
net OIMap := f -> "Width: "|net f.Width || "Assignment: "|net f.assignment

-- Verification method for OIMap
verifyData OIMap := f -> (
    if not sort keys f === sort {Width, assignment} then error("Expected keys {Width, assignment}, instead got "|toString keys f);
    if not instance(f.Width, ZZ) then error("Expected type ZZ for Width, instead got type "|toString class f.Width); 
    verifyData f.Width;

    bad := false;
    for i to #f.assignment - 1 do (
        entry := f.assignment#i;
        if not instance(entry, ZZ) or entry < 1 or entry > f.Width then ( bad = true; break ); -- Check that the entries are between 1 and f.Width
        if not i == 0 then if entry <= f.assignment#(i - 1) then ( bad = true; break ) -- Check that the entries are strictly increasing
    );

    if bad then error("Expected a list of strictly increasing positive integers between 1 and "|toString f.Width|", instead got "|toString f.assignment)
)

-- PURPOSE: Make a new OIMap
-- INPUT: '(n, L)', a width 'n' and a list 'L'
-- OUTPUT: An OIMap made from n and L
makeOIMap = method(TypicalValue => OIMap, Options => {VerifyData => true})
makeOIMap(ZZ, List) := opts -> (n, L) -> (
    ret := new OIMap from {Width => n, assignment => L};
    if opts.VerifyData then verifyData ret;
    ret
)

-- PURPOSE: Get all OI-maps between two widths
-- INPUT: '(m, n)', a width 'm' and a width 'n'
-- OUTPUT: A list of the OI-maps from m to n
getOIMaps = method(TypicalValue => List)
getOIMaps(ZZ, ZZ) := (m, n) -> (
    if n < m then return {};
    ret := new List;
    sets := subsets(set toList(1..n), m);
    for s in sets do ret = append(ret, makeOIMap(n, sort toList s, VerifyData => false));

    ret
)

-- PURPOSE: Compose two OI-maps
-- INPUT: '(f, g)', an OIMap 'f' and an OIMap 'g'
-- OUTPUT: The OIMap f(g)
composeOIMaps = method(TypicalValue => OIMap, Options => {VerifyData => true})
composeOIMaps(OIMap, OIMap) := opts -> (f, g) -> (
    if opts.VerifyData then scan({f, g}, verifyData);
    if not g.Width == #f.assignment then error "Maps cannot be composed due to incompatible source and target";
    L := new List;
    for i to #g.assignment - 1 do L = append(L, f.assignment#(g.assignment#i - 1));
    makeOIMap(f.Width, L, VerifyData => false)
)

--------------------------------------------------------------------------------
-- END: OIMap.m2 ---------------------------------------------------------------
--------------------------------------------------------------------------------