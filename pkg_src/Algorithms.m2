--------------------------------------------------------------------------------
-- BEGIN: Algorithms.m2 --------------------------------------------------------
--------------------------------------------------------------------------------

-- PURPOSE: Compute a remainder of a VectorInWidth modulo a List of VectorInWidths
-- INPUT: '(f, L)', a VectorInWidth 'f' and a List 'L'
-- OUTPUT: A remainder of f modulo L
remainder(VectorInWidth, List) := (f, L) -> (
    if #L == 0 then error "Expected nonempty List";

    if isZero f then return f;

    rem := f;
    while true do (
        divisionOccurred := false;
        for elt in L do (
            div := oiDivides(rem, elt);
            if div === false then continue;

            quot := div#0;
            moduleMap := getInducedModuleMap(freeOIModuleFromElement f, div#1);
            rem = rem - quot.ringElement * (moduleMap elt);

            if isZero rem then return rem;
            divisionOccurred = true;
            break
        );

        if not divisionOccurred then break
    );

    rem
)

-- PURPOSE: Compute the S-polynomial of two VectorInWidths
-- INPUT: '(f, g)', a VectorInWidth 'f' and a VectorInWidth 'g'
-- OUTPUT: The S-polynomial S(f, g)
-- COMMENT: Returns zero if either f or g is zero or if lcm(leadOITerm f, leadOITerm g) is zero
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

-- PURPOSE: Generate a List of OI-pairs from a List of VectorInWidths
-- INPUT: A List 'L'
-- OUTPUT: A List of OI-pairs made from L
-- COMMENT: Slow. This is the main bottleneck. Need to optimize.
oiPairs = method(TypicalValue => List, Options => {Verbose => false})
oiPairs List := opts -> L -> (
    if #L < 2  then error "Expected a List with at least 2 elements";

    ret := new List;
    for i to #L - 2 do (
        f := L#i;
        lotf := leadOITerm f;
        Widthf := widthOfElement f;
        for j from i + 1 to #L - 1 do (
            g := L#j;
            Widthg := widthOfElement g;
            lotg := leadOITerm g;
            if not lotf.basisIndex.idx == lotg.basisIndex.idx then continue; -- These will have lcm zero

            if opts.Verbose then print("Generating pairs for "|net f|" and "|net g);

            searchMin := max(Widthf, Widthg);
            searchMax := Widthf + Widthg;
            for i to searchMax - searchMin do (
                k := searchMax - i;
                oiMapsFromf := getOIMaps(Widthf, k);

                -- Given an OI-map out of f, we construct the corresponding OI-maps out of g
                for oiMapFromf in oiMapsFromf do (
                    base := set(1..k) - set oiMapFromf.assignment; -- Get the starting set

                    -- Now add back in the i-element subsets of oiMapFromf.assignment and make the pairs
                    for subset in subsets(oiMapFromf.assignment, i) do (
                        oiMapFromg := makeOIMap(k, sort toList(base + set subset));
                        if not composeOIMaps(oiMapFromf, lotf.basisIndex.oiMap) === composeOIMaps(oiMapFromg, lotg.basisIndex.oiMap) then continue; -- These will have lcm zero

                        if opts.Verbose then print("Found OI-maps "|net oiMapFromf|" and "|net oiMapFromg);

                        moduleMapFromf := getInducedModuleMap(freeOIModuleFromElement f, oiMapFromf);
                        moduleMapFromg := getInducedModuleMap(freeOIModuleFromElement g, oiMapFromg);

                        candidate := {moduleMapFromf f, moduleMapFromg g};
                        if not member(candidate, ret) then ret = append(ret, candidate) -- Avoid duplicates
                    )
                )
            )
        )
    );

    ret
)

-- PURPOSE: Compute a Groebner basis
-- INPUT: A List 'L' of VectorInWidths
-- OUTPUT: A Groebner basis made from L
-- COMMENT: Uses the OI-Buchberger's Algorithm
oiGB = method(TypicalValue => List, Options => {Verbose => false})
oiGB List := opts -> L -> (
    if #L == 0 then error "Expected a nonempty List";
    if #L == 1 then return L;
    
    ret := L;
    addedTotal := 0;
    while true do ( -- Terminates by a Noetherianity argument
        retTmp := ret;

        oipairs := oiPairs(ret, Verbose => opts.Verbose);
        encountered := new List;
        addedThisPhase := 0;
        for i to #oipairs - 1 do (
            s := spoly((oipairs#i)#0, (oipairs#i)#1);
            if member(s, encountered) then continue; -- Skip redundant S-polynomials
            encountered = append(encountered, s);

            if opts.Verbose then (
                print("On pair "|toString (i + 1)|" out of "|toString (#oipairs));
                print("Elements added so far this phase: "|toString addedThisPhase);
                print("Elements added total: "|toString addedTotal);
                print("Dividing "|net s|" by "|net ret)
            );

            rem := remainder(s, ret);
            if not isZero rem and not member(rem, ret) then (
                if opts.Verbose then print("Remainder: "|net rem);
                ret = append(ret, rem);
                addedThisPhase = addedThisPhase + 1;
                addedTotal = addedTotal + 1
            )
        );

        if ret === retTmp then return ret -- No new elements were added so we're done by the OI-Buchberger's Criterion
    )
)

-- PURPOSE: Check if a List is an OI-Groebner basis
-- INPUT: A List 'L' of VectorInWidths
-- OUTPUT: true if L is an OI-Groebner basis, false otherwise
isOIGB = method(TypicalValue => Boolean)
isOIGB List := L -> (
    if #L == 0 then return false;
    if #L == 1 then return true;

    for pair in oiPairs L do
        if not isZero remainder(spoly(pair#0, pair#1), L) then return false; -- If L were a GB, every element would have a unique remainder of zero
    
    true
)

--------------------------------------------------------------------------------
-- END: Algorithms.m2 ----------------------------------------------------------
--------------------------------------------------------------------------------