--------------------------------------------------------------------------------
-- FROM: OI.m2 -----------------------------------------------------------------
--------------------------------------------------------------------------------

-- Define the new type OIMap
OIMap = new Type of List;

-- PURPOSE: Check if a given OIMap is valid
-- INPUT: An OIMap 'oiMap'
-- OUTPUT: Nothing if oiMap is a valid OIMap, otherwise error
validateOIMap = method()
validateOIMap OIMap := oiMap -> (
    if #oiMap == 0 then return;

    bad := false;
    for i to #oiMap - 1 do (
        if not instance(oiMap#i, ZZ) or oiMap#i < 1 then (bad = true; break);
        if not i == 0 then if oiMap#i <= oiMap#(i - 1) then (bad = true; break);
    );

    if bad then error("Expected strictly increasing list of positive integers, not "|toString(oiMap));
)

-- Install comparison method for OIMaps (lex order)
OIMap ? OIMap := (m1, m2) -> (
    validateOIMap m1; validateOIMap m2;
    if not #m1 == #m2 then return symbol incomparable;
    if m1 === m2 then return symbol ==;
    
    for i to #m1 - 1 do if not m1#i == m2#i then return m1#i ? m2#i;
)

-- PURPOSE: Check if a given width is valid
-- INPUT: An integer 'n'
-- OUTPUT: Nothing if n is a valid width, otherwise error
validateWidth = method()
validateWidth ZZ := n -> if n < 0 then error("Expected nonnegative width, not "|toString(n));

-- PURPOSE: Get all OI-maps between two widths
-- INPUT: '(m, n)', a width 'm' and a width 'n'
-- OUTPUT: A list of OI-maps from m to n
-- COMMENT: Returns an empty list if n < m
getOIMaps = method(TypicalValue => List)
getOIMaps(ZZ, ZZ) := (m, n) -> (
    validateWidth m; validateWidth n;
    if n < m then return {};

    -- Generate OI-maps
    ret := new List;
    sets := subsets(set(toList(1..n)), m);
    for s in sets do ret = append(ret, new OIMap from sort(toList(s)));

    ret
)