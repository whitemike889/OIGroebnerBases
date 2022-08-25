-- Cache for storing OI-maps
oiMapCache = new MutableHashTable

-- Should be of the form {targWidth => ZZ, img => List}
OIMap = new Type of HashTable

net OIMap := f -> "Source: ["|net(#f.img)|"] Target: ["|net f.targWidth|"]" || "Image: "|net f.img

source OIMap := f -> toList(1..#f.img)
target OIMap := f -> toList(1..f.targWidth)
image OIMap := f -> f.img

-- Given an OI-map f, compute f(n)
OIMap ZZ := (f, n) -> f.img#(n - 1)

makeOIMap = method(TypicalValue => OIMap)
makeOIMap(ZZ, List) := (n, L) -> new OIMap from {targWidth => n, img => L}

-- Get the OI-maps between two widths
getOIMaps = method(TypicalValue => List)
getOIMaps(ZZ, ZZ) := (m, n) -> (
    if n < m then return {};
    
    -- Return the maps if they already exist
    if oiMapCache#?(m, n) then return oiMapCache#(m, n);

    sets := subsets(toList(1..n), m);
    ret := for i to #sets - 1 list new OIMap from {targWidth => n, img => sets#i};

    -- Store the maps
    oiMapCache#(m, n) = ret;

    ret
)

-- Given OI-maps f and g, compute f(g)
composeOIMaps = method(TypicalValue => OIMap)
composeOIMaps(OIMap, OIMap) := (f, g) -> (
    if not source f === target g then error "Maps cannot be composed due to incompatible source and target";
    L := for i in source g list f g i;
    new OIMap from {targWidth => f.targWidth, img => L}
)

-- Shorthand composition
OIMap OIMap := (f, g) -> composeOIMaps(f, g)