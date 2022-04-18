--------------------------------------------------------------------------------
-- FROM: OI.m2 -----------------------------------------------------------------
--------------------------------------------------------------------------------

-- PURPOSE: Check if a given width is valid
-- INPUT: An integer 'n'
-- OUTPUT: Nothing if n is a valid width, otherwise error
-- COMMENT: Unexported
validateWidth = method()
validateWidth ZZ := n -> (
    if n < 0 then error("Expected nonnegative width, not "|toString(n))
)

-- PURPOSE: Get all OI-maps between two widths
-- INPUT: '(m, n)', a width 'm' and a width 'n' with m ≤ n
-- OUTPUT: A list of OI-maps from m to n
-- COMMENT: Returns an empty list if n < m
-- COMMENT: We represent an OI-map from m to n as a length m list with strictly increasing entries in [n]
getOIMaps = method(TypicalValue => List)
getOIMaps(ZZ, ZZ) := (m, n) -> (
    validateWidth m; validateWidth n;
    if n < m then return {};

    ret := new List;
    sets := subsets(set(toList(1..n)), m);
    for s in sets do (
        ret = append(ret, sort(toList(s)))
    );

    ret
)