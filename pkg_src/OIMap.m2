-- Cache for storing OI-maps
oiMapCache = new MutableHashTable

-- PURPOSE: Define the new type OIMap
-- COMMENT: Should be of the form {Width => ZZ, assignment => List}
OIMap = new Type of HashTable
OIMap.synonym = "OI-map"

toString OIMap := f -> "width => "|toString f.Width|", assignment => "|toString f.assignment

net OIMap := f -> "Width: "|net f.Width || "Assignment: "|net f.assignment

source OIMap := f -> toList(1..#f.assignment)
target OIMap := f -> toList(1..f.Width)

-- PURPOSE: Make a new OIMap
-- INPUT: '(n, L)', a width 'n' and a list 'L'
-- OUTPUT: An OIMap made from n and L
makeOIMap = method(TypicalValue => OIMap)
makeOIMap(ZZ, List) := (n, L) -> new OIMap from {Width => n, assignment => L}

-- PURPOSE: Get all OI-maps between two widths
-- INPUT: '(m, n)', a width 'm' and a width 'n'
-- OUTPUT: A list of the OI-maps from m to n
getOIMaps = method(TypicalValue => List)
getOIMaps(ZZ, ZZ) := (m, n) -> (
    if n < m then return {};
    
    -- Return the maps if they already exist
    if oiMapCache#?(m, n) then return oiMapCache#(m, n);

    ret := new MutableList;
    sets := subsets(toList(1..n), m);
    for i to #sets - 1 do ret#i = new OIMap from {Width => n, assignment => sets#i};
    ret = toList ret;

    -- Store the maps
    oiMapCache#(m, n) = ret;

    ret
)

-- PURPOSE: Compose two OI-maps
-- INPUT: '(f, g)', an OIMap 'f' and an OIMap 'g'
-- OUTPUT: The OIMap f(g)
composeOIMaps = method(TypicalValue => OIMap)
composeOIMaps(OIMap, OIMap) := (f, g) -> (
    if not #f.assignment == g.Width then error "Maps cannot be composed due to incompatible source and target";
    L := new MutableList;
    for i to #g.assignment - 1 do L#i = f.assignment#(g.assignment#i - 1);
    new OIMap from {Width => f.Width, assignment => toList L}
)