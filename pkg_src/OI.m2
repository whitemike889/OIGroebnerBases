--------------------------------------------------------------------------------
-- BEGIN: OI.m2 ----------------------------------------------------------------
--------------------------------------------------------------------------------

-- PURPOSE: Check if a given integer is nonnegative
-- INPUT: An integer 'n'
-- OUTPUT: Nothing if 0 ≤ n, otherwise error
assertValid ZZ := n -> if n < 0 then error("Expected a nonnegative integer, instead got "|toString n)

-- PURPOSE: Define the new type OIMap
-- COMMENT: Should be of the form '{n, {...}}' where n is the target width and {...} is a (possibly empty) list of strictly increasing positive integers between 1 and n
OIMap = new Type of List

-- PURPOSE: Check if a given OIMap is valid
-- INPUT: An OIMap 'f'
-- OUTPUT: Nothing if f is a valid OI-map, otherwise error
assertValid OIMap := f -> (
    if not #f == 2 or not instance(f#0, ZZ) or not instance(f#1, List) then error("Expected a list of the form {n, {...}} where n is a nonnegative integer and {...} is a (possibly empty) list of strictly increasing positive integers between 1 and n, instead got "|toString f);
    assertValid f#0;

    bad := false;
    for i to #(f#1) - 1 do (
        if not instance((f#1)#i, ZZ) or (f#1)#i < 1 or (f#1)#i > f#0 then (bad = true; break); -- Check that the entries are between 1 and f#0
        if not i == 0 then if (f#1)#i <= (f#1)#(i - 1) then (bad = true; break) -- Check that the entries are strictly increasing
    );

    if bad then error("Expected a list of strictly increasing positive integers between 1 and "|toString f#0|", not "|toString f#1)
)

-- PURPOSE: Make a new OIMap
-- INPUT: '(n, L)', a width 'n' and a list 'L'
-- OUTPUT: An OIMap made from n and L
oiMap = method(TypicalValue => OIMap)
oiMap(ZZ, List) := (n, L) -> (
    f := new OIMap from {n, L};
    assertValid f;
    f
)

-- PURPOSE: Get all OI-maps between two widths
-- INPUT: '(m, n)', a width 'm' and a width 'n'
-- OUTPUT: A list of the OI-maps from m to n
-- COMMENT: Returns the empty list if n < m
getOIMaps = method(TypicalValue => List)
getOIMaps(ZZ, ZZ) := (m, n) -> (
    scan({m, n}, assertValid);
    if n < m then return {};

    -- Generate OI-maps
    ret := new List;
    sets := subsets(set toList(1..n), m);
    for s in sets do ret = append(ret, oiMap(n, sort toList s));

    ret
)

--------------------------------------------------------------------------------
-- END: OI.m2 ------------------------------------------------------------------
--------------------------------------------------------------------------------