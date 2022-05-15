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

-- Compute the S-polynomial of two VectorInWidths
spoly = method(TypicalValue => VectorInWidth)
spoly(VectorInWidth, VectorInWidth) := (f, g) -> (
    Widthf := widthOfElement f;
    Widthg := widthOfElement g;
    if not Widthf == Widthg then error "Vectors must belong to the same width";

    freeOIModf := freeOIModuleFromElement f;
    freeOIModg := freeOIModuleFromElement g;
    if not freeOIModf === freeOIModg then error "Vectors must belong to the same free OI-module";
    freeMod := getFreeModuleInWidth(freeOIModf, Widthf);

    if isZero f or isZero g then return 0_freeMod;

    lotf := leadOITerm f;
    lotg := leadOITerm g;
    lcmfg := lcm(lotf, lotg);
    if isZero lcmfg then return 0_freeMod;
    (lcmfg.ringElement // lotf.ringElement)*f - (lcmfg.ringElement // lotg.ringElement)*g
)

--------------------------------------------------------------------------------
-- END: Algorithms.m2 ----------------------------------------------------------
--------------------------------------------------------------------------------