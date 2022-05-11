--------------------------------------------------------------------------------
-- BEGIN: Terms.m2 -------------------------------------------------------------
--------------------------------------------------------------------------------

-- Define the new type BasisIndex
-- COMMENT: Should be of the form {freeOIMod => FreeOIModule, oiMap => OIMap, idx => ZZ}
BasisIndex = new Type of HashTable
BasisIndex.synonym = "basis index"

-- PURPOSE: Make a new BasisIndex
-- INPUT: '(F, f, i)', a FreeOIModule 'F', an OIMap 'f' and an index 'i'
-- OUTPUT: A BasisIndex made from F, f and i
makeBasisIndex = method(TypicalValue => BasisIndex)
makeBasisIndex(FreeOIModule, OIMap, ZZ) := (F, f, i) -> new BasisIndex from {freeOIMod => F, oiMap => f, idx => i}

-- Define the new type OITerm
-- COMMENT: Should be of the form {ringElement => RingElement, basisIndex => BasisIndex}
OITerm = new Type of HashTable
OITerm.synonym = "OI-term"

-- PURPOSE: Make a new OITerm
-- INPUT: '(elt, b)', a RingElement 'elt' and a BasisIndex 'b'
-- OUTPUT: An OITerm made from elt and b
makeOITerm = method(TypicalValue => OITerm)
makeOITerm(RingElement, BasisIndex) := (elt, b) -> new OITerm from {ringElement => elt, basisIndex => b}

-- Install net method for OITerm
net OITerm := f -> net f.ringElement | net f.basisIndex.freeOIMod.basisSym_(toString f.basisIndex.oiMap.Width, toString f.basisIndex.oiMap.assignment, f.basisIndex.idx)

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
        if not idxf == idxg then ( if idxf < idxg then return symbol > else return symbol < );
        if not oiMapf.Width == oiMapg.Width then return oiMapf.Width ? oiMapg.Width;
        if not oiMapf.assignment == oiMapg.assignment then return oiMapf.assignment ? oiMapg.assignment;

        use class eltf; -- Note: since oiMapf.Width = oiMapg.Width we have class eltf = class eltg
        return eltf ? eltg
    )
    else if instance(monOrder, FreeOIModuleMap) then ( -- SCHREYER ORDER
        -- TODO: IMPLEMENT THIS
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
getOITermsFromVector = method(TypicalValue => List)
getOITermsFromVector VectorInWidth := f -> (
    freeOIMod := (class f).freeOIMod;
    Width := (class f).Width;
    freeMod := getFreeModuleInWidth(freeOIMod, Width);
    termList := new List;
    entryList := entries f;

    for i to #entryList - 1 do (
        if entryList#i == 0 then continue;

        basisElement := freeMod.basisElements#i;
        termList = append(termList, makeOITerm(entryList#i, basisElement.basisIndex))
    );

    reverse sort termList
)

-- PURPOSE: Get the leading OITerm from a vector
-- INPUT: A VectorInWidth 'f'
-- OUTPUT: The largest OITerm in f
leadOITerm = method(TypicalValue => OITerm)
leadOITerm Vector := f -> (
    oiTerms := getOITermsFromVector f;
    if #oiTerms == 0 then return null;
    oiTerms#0
)

--------------------------------------------------------------------------------
-- END: Terms.m2 ---------------------------------------------------------------
--------------------------------------------------------------------------------