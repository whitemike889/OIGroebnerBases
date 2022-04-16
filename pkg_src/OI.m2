--------------------------------------------------------------------------------
-- FROM: OI.m2 -----------------------------------------------------------------
--------------------------------------------------------------------------------

-- PURPOSE: Get all OI-maps between two widths
-- INPUT: '(m, n)', a width 'm' and a width 'n' with m ≤ n
-- OUTPUT: A list of OI-maps from m to n
-- COMMENT: Returns an empty list if n < m or either m or n are negative
-- COMMENT: We represent an OI-map from m to n as a length m list with strictly increasing entries in [n]
getOIMaps = method(TypicalValue => List)
getOIMaps(ZZ, ZZ) := (m, n) -> (
    if n < m or (m < 0 or n < 0) then return {};

    ret := new MutableList;
    sets := subsets(set(toList(1..n)), m);
    for s in sets do (
        ret = append(ret, sort(toList(s)))
    );

    toList(ret)
)