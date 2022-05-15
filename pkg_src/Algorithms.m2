--------------------------------------------------------------------------------
-- BEGIN: Algorithms.m2 --------------------------------------------------------
--------------------------------------------------------------------------------

-- Compute a remainder of a VectorInWidth modulo a List of VectorInWidths
remainder(VectorInWidth, List) := (f, L) -> (
    if #L == 0 then error "Expected nonempty List";

    rem := f;
    for elt in L do (
        div := oiDivides(f, elt);
        if div === false then continue;
        quot := div#0;
        moduleMap := getInducedModuleMap(freeOIModuleFromElement f, div#1);
        rem = rem - quot.ringElement * (moduleMap elt)
    );

    rem
)

--------------------------------------------------------------------------------
-- END: Algorithms.m2 ----------------------------------------------------------
--------------------------------------------------------------------------------