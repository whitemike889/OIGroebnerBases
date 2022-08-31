-- Should be of the form {freeOIMod => FreeOIModule, oiMap => OIMap, idx => ZZ}
BasisIndex = new Type of HashTable

makeBasisIndex = method(TypicalValue => BasisIndex)
makeBasisIndex(FreeOIModule, OIMap, ZZ) := (F, f, i) -> new BasisIndex from {freeOIMod => F, oiMap => f, idx => i}

-- Should be of the form {ringElement => RingElement, basisIndex => BasisIndex}
OITerm = new Type of HashTable

makeOITerm = method(TypicalValue => OITerm)
makeOITerm(RingElement, BasisIndex) := (elt, b) -> new OITerm from {ringElement => elt, basisIndex => b}

net OITerm := f -> (
    local ringElementNet;
    if #terms f.ringElement == 1 or #terms f.ringElement == 0 then ringElementNet = net f.ringElement
    else ringElementNet = "("|net f.ringElement|")";
    ringElementNet | net f.basisIndex.freeOIMod.basisSym_(toString f.basisIndex.oiMap.targWidth, toString f.basisIndex.oiMap.img, f.basisIndex.idx)
)

isZero OITerm := f -> f.ringElement === 0_(class f.ringElement)
isZero RingElement := f -> f === 0_(class f)

-- Comparison method for OITerm
OITerm ? OITerm := (f, g) -> (
    if f === g then return symbol ==;

    eltf := f.ringElement; eltg := g.ringElement;
    bf := f.basisIndex; bg := g.basisIndex;
    oiMapf := bf.oiMap; oiMapg := bg.oiMap;
    idxf := bf.idx; idxg := bg.idx;

    if not bf.freeOIMod === bg.freeOIMod then return incomparable;
    freeOIMod := bf.freeOIMod;

    monOrder := getMonomialOrder freeOIMod;
    if monOrder === Lex then ( -- LEX ORDER
        if not idxf === idxg then if idxf < idxg then return symbol > else return symbol <;
        if not oiMapf.targWidth === oiMapg.targWidth then return oiMapf.targWidth ? oiMapg.targWidth;
        if not oiMapf.img === oiMapg.img then return oiMapf.img ? oiMapg.img;

        use class eltf; -- Note: since oiMapf.targWidth = oiMapg.targWidth we have class eltf === class eltg
        return eltf ? eltg
    )
    else if instance(monOrder, List) then ( -- SCHREYER ORDER
        -- TODO: Implement this
    )
    else error "monomial order not supported"
)

-- Comparison method for VectorInWidth
VectorInWidth ? VectorInWidth := (f, g) -> leadOITerm f ? leadOITerm g

makeBasisElement = method(TypicalValue => OITerm)
makeBasisElement BasisIndex := b -> (
    one := 1_(getAlgebraInWidth(b.freeOIMod.polyOIAlg, b.oiMap.targWidth));
    new OITerm from {ringElement => one, basisIndex => b}
)

getOITermsFromVector = method(TypicalValue => List, Options => {CombineLikeTerms => false})
getOITermsFromVector VectorInWidth := opts -> f -> (
    if isZero f then error "the zero element has no OI-terms";
    freeMod := class f;
    entryList := entries f;

    if opts.CombineLikeTerms then reverse sort for i to #entryList - 1 list (
        if isZero entryList#i then continue;
        makeOITerm(entryList#i, (freeMod.basisElements#i).basisIndex)
    ) else reverse sort flatten for i to #entryList - 1 list (
        if isZero entryList#i then continue;
        for term in terms entryList#i list makeOITerm(term, (freeMod.basisElements#i).basisIndex)
    )
)

getVectorFromOITerms = method(TypicalValue => VectorInWidth)
getVectorFromOITerms List := L -> (
    if #L == 0 then error("getVectorFromOITerms expects a nonempty input");
    Width := (L#0).basisIndex.oiMap.targWidth;
    freeOIMod := (L#0).basisIndex.freeOIMod;
    freeMod := getFreeModuleInWidth(freeOIMod, Width);
    vect := 0_freeMod;

    for oiTerm in L do (
        ringElement := oiTerm.ringElement;
        basisElement := makeBasisElement oiTerm.basisIndex;
        vect = vect + ringElement * freeMod_(freeMod.basisElementPositions#basisElement)
    );
    
    vect
)

leadOITerm = method(TypicalValue => OITerm)
leadOITerm VectorInWidth := f -> (
    if isZero f then error "the zero element has no lead OI-term";
    oiTerms := getOITermsFromVector f;
    oiTerms#0
)

leadTerm VectorInWidth := f -> (
    if isZero f then return f;
    loitf := leadOITerm f;
    getVectorFromOITerms {loitf}
)

leadCoefficient VectorInWidth := f -> (
    if isZero f then return 0_((freeOIModuleFromElement f).polyOIAlg.baseField);
    loitf := leadOITerm f;
    leadCoefficient loitf.ringElement
)

leadMonomial VectorInWidth := f -> (
    if isZero f then error "the zero element has no lead monomial";
    loitf := leadOITerm f;
    getVectorFromOITerms {makeOITerm(loitf.ringElement // leadCoefficient loitf.ringElement, loitf.basisIndex)}
)

-- Scale a VectorInWidth by a number
VectorInWidth // Number := (f, r) -> (
    if isZero f then return f;
    oiTerms := getOITermsFromVector f;
    getVectorFromOITerms for oiTerm in oiTerms list makeOITerm(oiTerm.ringElement // r_(class oiTerm.ringElement), oiTerm.basisIndex)
)

-- Tries to divide f by g
-- Returns a HashTable of the form {quo => RingElement, oiMap => OIMap}
-- Returns {quo => 0, oiMap => null} if division does not occur
oiTermDiv = method(TypicalValue => HashTable)
oiTermDiv(OITerm, OITerm) := (f, g) -> (
    freeOIModf := f.basisIndex.freeOIMod;
    freeOIModg := g.basisIndex.freeOIMod;

    retZero := new HashTable from {quo => 0_(class f.ringElement), oiMap => null};
    if not freeOIModf === freeOIModg then return retZero;

    Widthf := f.basisIndex.targWidth;
    Widthg := g.basisIndex.targWidth;
    if Widthf < Widthg then return retZero;
    if Widthf === Widthg then (
        if not f.basisIndex === g.basisIndex then return retZero;
        if isZero(f.ringElement % g.ringElement) then return new HashTable from {quo => f.ringElement // g.ringElement, oiMap => (getOIMaps(Widthg, Widthf))#0} else return retZero
    );

    oiMaps := getOIMaps(Widthg, Widthf);

    -- TODO: Finish this

    retZero
)

lcm(OITerm, OITerm) := (f, g) -> (
    if not f.basisIndex === g.basisIndex then return makeOITerm(0_(class f.ringElement), f.basisIndex);

    makeOITerm(lcm(f.ringElement // leadCoefficient f.ringElement, g.ringElement // leadCoefficient g.ringElement), f.basisIndex)
)

lcm(VectorInWidth, VectorInWidth) := (f, g) -> if isZero f then f else if isZero g then g else getVectorFromOITerms {lcm(leadOITerm f, leadOITerm g)}

terms VectorInWidth := f -> (
    if isZero f then return {};
    oiTerms := getOITermsFromVector f;
    for oiTerm in oiTerms list getVectorFromOITerms {oiTerm}
)