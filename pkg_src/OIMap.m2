--------------------------------------------------------------------------------
-- BEGIN: OIMap.m2 -------------------------------------------------------------
--------------------------------------------------------------------------------

-- PURPOSE: Check if a given integer is nonnegative
-- INPUT: An integer 'n'
-- OUTPUT: Nothing if 0 ≤ n, otherwise error
assertValid ZZ := n -> if n < 0 then error("Expected a nonnegative integer, instead got "|toString n)

-- PURPOSE: Define the new type OIMap
-- COMMENT: Should be of the form {Width => ZZ, assignment => List}
OIMap = new Type of HashTable

-- Install toString method for OIMap
toString OIMap := f -> toString new List from {f.Width, f.assignment}

-- Install net method for OIMap
net OIMap := f -> "Width: "|net f.Width || "Assignment: "|net f.assignment

-- Validation method for OIMap
assertValid OIMap := f -> (
    if not sort keys f === sort {Width, assignment} then error("Expected keys {Width, assignment}, instead got "|toString keys f);
    if not instance(f.Width, ZZ) then error("Expected type ZZ for Width, instead got type "|toString class f.Width); 
    assertValid f.Width;

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
makeOIMap = method(TypicalValue => OIMap, Options => {AssertValid => true})
makeOIMap(ZZ, List) := opts -> (n, L) -> (
    f := new OIMap from {Width => n, assignment => L};
    if opts.AssertValid then assertValid f;
    f
)

-- PURPOSE: Get all OI-maps between two widths
-- INPUT: '(m, n)', a width 'm' and a width 'n'
-- OUTPUT: A list of the OI-maps from m to n
-- COMMENT: Returns the empty list if n < m
getOIMaps = method(TypicalValue => List, Options => {AssertValid => true})
getOIMaps(ZZ, ZZ) := opts -> (m, n) -> (
    if opts.AssertValid then scan({m, n}, assertValid);
    if n < m then return {};

    -- Generate OI-maps
    ret := new List;
    sets := subsets(set toList(1..n), m);
    for s in sets do ret = append(ret, makeOIMap(n, sort toList s));

    ret
)

--------------------------------------------------------------------------------
-- END: OIMap.m2 ---------------------------------------------------------------
--------------------------------------------------------------------------------