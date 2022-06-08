-- Define the new type BasisIndex
-- COMMENT: Should be of the form {freeOIMod => FreeOIModule, oiMap => OIMap, idx => ZZ}
BasisIndex = new Type of HashTable

-- PURPOSE: Make a new BasisIndex
-- INPUT: '(F, f, i)', a FreeOIModule 'F', an OIMap 'f' and an index 'i'
-- OUTPUT: A BasisIndex made from F, f and i
-- COMMENT: i should start at 1
makeBasisIndex = method(TypicalValue => BasisIndex)
makeBasisIndex(FreeOIModule, OIMap, ZZ) := (F, f, i) -> new BasisIndex from {freeOIMod => F, oiMap => f, idx => i}

-- Define the new type OITerm
-- COMMENT: Should be of the form {ringElement => RingElement, basisIndex => BasisIndex}
OITerm = new Type of HashTable

-- PURPOSE: Make a new OITerm
-- INPUT: '(elt, b)', a RingElement 'elt' and a BasisIndex 'b'
-- OUTPUT: An OITerm made from elt and b
makeOITerm = method(TypicalValue => OITerm)
makeOITerm(RingElement, BasisIndex) := (elt, b) -> new OITerm from {ringElement => elt, basisIndex => b}

net OITerm := f -> (
    local ringElementNet;
    if #terms f.ringElement == 1 or #terms f.ringElement == 0 then ringElementNet = net f.ringElement
    else ringElementNet = "("|net f.ringElement|")";
    ringElementNet | net f.basisIndex.freeOIMod.basisSym_(toString f.basisIndex.oiMap.Width, toString f.basisIndex.oiMap.assignment, f.basisIndex.idx)
)

-- Comparison method for OITerm
OITerm ? OITerm := (f, g) -> (
    if f === g then return symbol ==;

    eltf := f.ringElement; eltg := g.ringElement;
    bf := f.basisIndex; bg := g.basisIndex;
    oiMapf := bf.oiMap; oiMapg := bg.oiMap;
    idxf := bf.idx; idxg := bg.idx;

    if not bf.freeOIMod === bg.freeOIMod then return incomparable;
    freeOIMod := bf.freeOIMod;

    monOrder := freeOIMod.monOrder#0;
    if monOrder === Lex then ( -- LEX ORDER
        if not idxf == idxg then if idxf < idxg then return symbol > else return symbol <;
        if not oiMapf.Width == oiMapg.Width then return oiMapf.Width ? oiMapg.Width;
        if not oiMapf.assignment == oiMapg.assignment then return oiMapf.assignment ? oiMapg.assignment;

        use class eltf; -- Note: since oiMapf.Width = oiMapg.Width we have class eltf = class eltg
        return eltf ? eltg
    )
    else if instance(monOrder, FreeOIModuleMap) then ( -- SCHREYER ORDER
        freeOIModuleMap := monOrder;
        imagef := freeOIModuleMap {f};
        imageg := freeOIModuleMap {g};
        if not leadOITerm imagef === leadOITerm imageg then return leadOITerm imagef ? leadOITerm imageg;
        if not idxf == idxg then if idxf < idxg then return symbol > else return symbol <;
        if not oiMapf.Width == oiMapg.Width then return oiMapf.Width ? oiMapg.Width;
        if not oiMapf.assignment == oiMapg.assignment then return oiMapf.assignment ? oiMapg.assignment;
        return symbol ==;
    )
    else error "Monomial order not supported"
)

-- PURPOSE: Make a basis element
-- INPUT: A BasisIndex 'b'
-- OUTPUT: An OITerm with ringElement = 1
makeBasisElement = method(TypicalValue => OITerm)
makeBasisElement BasisIndex := b -> (
    one := 1_(getAlgebraInWidth(b.freeOIMod.polyOIAlg, b.oiMap.Width));
    new OITerm from {ringElement => one, basisIndex => b}
)

-- PURPOSE: Convert an element from vector form to a list of OITerms
-- INPUT: A VectorInWidth 'f'
-- OUTPUT: A List of OITerms corresponding to the terms of f sorted from greatest to least
-- COMMENT: "Combine => true" will combine like terms (used for printing vectors)
getOITermsFromVector = method(TypicalValue => List, Options => {Combine => false})
getOITermsFromVector VectorInWidth := opts -> f -> (
    freeOIMod := (class f).freeOIMod;
    Width := (class f).Width;
    freeMod := getFreeModuleInWidth(freeOIMod, Width);
    termList := new MutableList;
    entryList := entries f;

    k := 0;
    for i to #entryList - 1 do (
        if entryList#i == 0 then continue;

        basisElement := freeMod.basisElements#i;
        if opts.Combine then (
            termList#k = makeOITerm(entryList#i, basisElement.basisIndex);
            k = k + 1
        ) else (
            termsInEntry := terms entryList#i;
            for term in termsInEntry do ( termList#k = makeOITerm(term, basisElement.basisIndex); k = k + 1 )
        )
    );

    reverse sort toList termList
)

-- PURPOSE: Convert an element from a list of OITerms to vector form
-- INPUT: A List 'L' of OITerms
-- OUTPUT: A VectorInWidth made from L
getVectorFromOITerms = method(TypicalValue => VectorInWidth)
getVectorFromOITerms List := L -> (
    if #L == 0 then return null;
    Width := (L#0).basisIndex.oiMap.Width;
    freeOIMod := (L#0).basisIndex.freeOIMod;
    freeMod := getFreeModuleInWidth(freeOIMod, Width);
    vect := 0_freeMod;

    for oiTerm in L do (
        ringElement := oiTerm.ringElement;
        basisElement := makeBasisElement oiTerm.basisIndex;
        pos := position(freeMod.basisElements, elt -> elt === basisElement);
        vect = vect + ringElement * freeMod_pos
    );
    
    vect
)

-- PURPOSE: Get the leading OITerm from a vector
-- INPUT: A VectorInWidth 'f'
-- OUTPUT: The largest OITerm in f
leadOITerm = method(TypicalValue => OITerm)
leadOITerm VectorInWidth := f -> (
    oiTerms := getOITermsFromVector f;
    if #oiTerms == 0 then return null;
    oiTerms#0
)

-- PURPOSE: Divide one OI-term by another
oiTermDiv = method(TypicalValue => HashTable)

-- INPUT: '(f, g)', an OITerm 'f' and an OITerm 'g'
-- OUTPUT: A HashTable of the form {quo => RingElement, oiMap => OIMap}
-- COMMENT: Returns {quo => 0, oiMap => null} if division does not occur
oiTermDiv(OITerm, OITerm) := (f, g) -> (
    freeOIModf := f.basisIndex.freeOIMod;
    freeOIModg := g.basisIndex.freeOIMod;

    retZero := new HashTable from {quo => 0_(class f.ringElement), oiMap => null};
    if not freeOIModf === freeOIModg then return retZero;

    Widthf := f.basisIndex.oiMap.Width;
    Widthg := g.basisIndex.oiMap.Width;
    if Widthf < Widthg then return retZero;
    if Widthf == Widthg then (
        if not f.basisIndex === g.basisIndex then return retZero;
        if f.ringElement % g.ringElement == 0 then return new HashTable from {quo => f.ringElement // g.ringElement, oiMap => (getOIMaps(Widthg, Widthf))#0} else return retZero
    );

    oiMaps := getOIMaps(Widthg, Widthf);
    for oimap in oiMaps do (
        moduleMap := getInducedModuleMap(freeOIModf, oimap);
        imageg := leadOITerm moduleMap {g};
        if not imageg.basisIndex === f.basisIndex then continue;
        if f.ringElement % imageg.ringElement == 0 then return new HashTable from {quo => f.ringElement // imageg.ringElement, oiMap => oimap} else continue
    );

    retZero
)

-- INPUT: '(f, g)', a VectorInWidth 'f' and a VectorInWidth 'g'
-- OUTPUT: Performs oiTermDiv on lt(f) and lt(g)
oiTermDiv(VectorInWidth, VectorInWidth) := (f, g) -> oiTermDiv(leadOITerm f, leadOITerm g)

-- PURPOSE: Get the least common multiple of two OITerms
-- INPUT: '(f, g)', an OITerm 'f' and an OITerm 'g'
-- OUTPUT: The LCM of f and g
lcm(OITerm, OITerm) := (f, g) -> (
    if not f.basisIndex === g.basisIndex then return makeOITerm(0_(class f.ringElement), f.basisIndex);

    makeOITerm(lcm(f.ringElement // leadCoefficient f.ringElement, g.ringElement // leadCoefficient g.ringElement), f.basisIndex)
)

-- PURPOSE: Get the least common multiple of the lead OI-term of two VectorInWidths
-- INPUT: '(f, g)', a VectorInWidth 'f' and a VectorInWidth 'g'
-- OUTPUT: The LCM of lt(f) and lt(g)
lcm(VectorInWidth, VectorInWidth) := (f, g) -> lcm(leadOITerm f, leadOITerm g)

-- Check if an OITerm is zero
isZero OITerm := f -> f.ringElement == 0_(class f.ringElement)

-- Check if a RingElement is zero
isZero RingElement := f -> f == 0_(class f)

-- Get the terms in a VectorInWidth
terms VectorInWidth := f -> (
    oiTerms := getOITermsFromVector f;
    for oiTerm in oiTerms list getVectorFromOITerms {oiTerm}
)