--------------------------------------------------------------------------------
-- BEGIN: TermsAndMonomials.m2 -------------------------------------------------
--------------------------------------------------------------------------------

-- Define the new type BasisIndex
-- COMMENT: Should be of the form {freeOIMod => FreeOIModule, oiMap => OIMap, idx => ZZ}
BasisIndex = new Type of HashTable
BasisIndex.synonym = "basis index"

-- PURPOSE: Make a new BasisIndex
-- INPUT: '(F, f, i)', a FreeOIModule 'F', an OIMap 'f' and an index 'i'
-- OUTPUT: A BasisIndex made from F, f and i
makeBasisIndex = method(TypicalValue => BasisIndex, Options => {VerifyData => true})
makeBasisIndex(FreeOIModule, OIMap, ZZ) := opts -> (F, f, i) -> (
    ret := new BasisIndex from {freeOIMod => F, oiMap => f, idx => i};
    if opts.VerifyData then verifyData ret;
    ret
)

-- Verification method for BasisIndex
verifyData BasisIndex := b -> (
    if not sort keys b === sort {freeOIMod, oiMap, idx} then error("Expected keys {freeOIMod, oiMap, idx}, instead got "|toString keys b);
    if not instance(b.freeOIMod, FreeOIModule) then error("Expected type FreeOIModule for freeOIMod, instead got type "|toString class b.freeOIMod);
    if not instance(b.oiMap, OIMap) then error("Expected type OIMap for oiMap, instead got type "|toString class b.oiMap);
    if not instance(b.idx, ZZ) then error("Expected type ZZ for idx, instead got type "|toString class b.idx);
    scan({b.freeOIMod, b.oiMap}, verifyData);

    genWidths := b.freeOIMod.genWidths;
    oiMap := b.oiMap;
    assignment := oiMap.assignment;
    idx := b.idx;

    if not (idx <= #genWidths and idx >= 1) then error("Expected idx between 1 and #genWidths = "|toString #genWidths|", instead got "|toString idx);
    if not #assignment == genWidths#(idx - 1) then error("Expected OIMap with source = genWidths#"|toString(idx - 1)|", instead got "|toString oiMap)
)

-- Define the new type OITerm
-- COMMENT: Should be of the form {ringElement => RingElement, basisIndex => BasisIndex}
OITerm = new Type of HashTable
OITerm.synonym = "OI-term"

-- PURPOSE: Make a new OITerm
-- INPUT: '(elt, b)', a RingElement 'elt' and a BasisIndex 'b'
-- OUTPUT: An OITerm made from elt and b
makeOITerm = method(TypicalValue => OITerm, Options => {VerifyData => true})
makeOITerm(RingElement, BasisIndex) := opts -> (elt, b) -> (
    ret := new OITerm from {ringElement => elt, basisIndex => b};
    if opts.VerifyData then verifyData ret;
    ret
)

-- Install net method for OITerm
net OITerm := f -> net f.ringElement | net f.basisIndex.freeOIMod.basisSym_(toString f.basisIndex.oiMap, f.basisIndex.idx)

-- Verification method for OITerm
verifyData OITerm := f -> (
    if not sort keys f === sort {ringElement, basisIndex} then error("Expected keys {ringElement, basisIndex}, instead got "|toString keys f);
    if not instance(f.ringElement, RingElement) then error("Expected type RingElement for ringElement, instead got "|toString class f.ringElement);
    if not instance(f.basisIndex, BasisIndex) then error("Expected type BasisIndex for basisIndex, instead got "|toString class f.basisIndex);
    verifyData f.basisIndex;
    
    elt := f.ringElement;
    freeOIMod := f.basisIndex.freeOIMod;
    Width := f.basisIndex.oiMap.Width;

    coeffs := ring getFreeModuleInWidth(freeOIMod, Width, VerifyData => false); -- Or getAlgebraInWidth(freeOIMod.polyOIAlg, Width);
    if not class elt === coeffs then error("Expected element of "|toString coeffs|", instead got "|toString elt|" which is an element of "|class elt);
    if not #terms elt == 1 then error("Expected a term, instead got "|toString elt)
)

-- Define the new type OIMonomial
-- COMMENT: Should be of the form {ringElement => RingElement, basisIndex => BasisIndex}
OIMonomial = new Type of OITerm
OIMonomial.synonym = "OI-monomial"

-- PURPOSE: Make a new OIMonomial
-- INPUT: '(elt, b)', a RingElement 'elt' and a BasisIndex 'b'
-- OUTPUT: An OIMonomial made from elt and b
makeOIMonomial = method(TypicalValue => OIMonomial, Options => {VerifyData => true})
makeOIMonomial(RingElement, BasisIndex) := opts -> (elt, b) -> (
    ret := new OIMonomial from {ringElement => elt, basisIndex => b};
    if opts.VerifyData then verifyData ret;
    ret
)

-- Verification method for OIMonomial
verifyData OIMonomial := f -> (
    verifyData new OITerm from f;
    
    elt := f.ringElement;
    baseField := f.basisIndex.freeOIMod.polyOIAlg.baseField;
    if not leadCoefficient elt == 1_baseField then error("Expected lead coefficient of 1, instead got "|toString leadCoefficient elt)
)

-- Comparison method for OIMonomial
OIMonomial ? OIMonomial := (f, g) -> (
    if f === g then return symbol ==;

    eltf := f.ringElement; eltg := g.ringElement;
    bf := f.basisIndex; bg := g.basisIndex;
    oiMapf := bf.oiMap; oiMapg := bg.oiMap;
    idxf := bf.idx; idxg := bg.idx;

    if not bf.freeOIMod === bg.freeOIMod then return incomparable;
    freeOIMod := bf.freeOIMod;

    monOrder := freeOIMod.monOrder#0;
    if monOrder === Lex then ( -- LEX ORDER
        if not idxf == idxg then ( if idxf < idxg then return symbol > else return symbol < );
        if not oiMapf.Width == oiMapg.Width then return oiMapf.Width ? oiMapg.Width;
        if not oiMapf.assignment == oiMapg.assignment then return oiMapf.assignment ? oiMapg.assignment;

        use class eltf; -- Note: since oiMapf.Width = oiMapg.Width we have class eltf = class eltg
        return eltf ? eltg
    )
    else if instance(monOrder, SchreyerMonomialOrder) then ( -- SCHREYER ORDER
        -- TODO: IMPLEMENT THIS
    )
    else error "Monomial order not supported"
)

-- Define the new type OIBasisElement
-- COMMENT: Should be of the form {ringElement => RingElement, basisIndex => BasisIndex}
OIBasisElement = new Type of OIMonomial
OIBasisElement.synonym = "OI-basis element"

-- PURPOSE: Make a new OIBasisElement
-- INPUT: A BasisIndex 'b'
-- OUTPUT: An OIBasisElement made from b
makeOIBasisElement = method(TypicalValue => OIBasisElement, Options => {VerifyData => true})
makeOIBasisElement BasisIndex := opts -> b -> (
    if opts.VerifyData then verifyData b;

    one := 1_(ring getFreeModuleInWidth(b.freeOIMod, b.oiMap.Width, VerifyData => false));
    new OIBasisElement from makeOIMonomial(one, b, VerifyData => false)
)

-- Verification method for OIBasisElement
verifyData OIBasisElement := f -> (
    verifyData new OITerm from f;

    elt := f.ringElement;
    b := f.basisIndex;
    one := 1_(ring getFreeModuleInWidth(b.freeOIMod, b.oiMap.Width, VerifyData => false));
    if not elt === one then error("Expected ringElement = 1, instead got "|toString elt)
)

--------------------------------------------------------------------------------
-- END: TermsAndMonomials.m2 ---------------------------------------------------
--------------------------------------------------------------------------------