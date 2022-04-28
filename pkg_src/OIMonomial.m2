--------------------------------------------------------------------------------
-- BEGIN: OIMonomial.m2 --------------------------------------------------------
--------------------------------------------------------------------------------

-- Define the new type BasisIndex
BasisIndex = new Type of List

-- PURPOSE: Make a new BasisIndex
-- INPUT: '(F, f, i)', a FreeOIModule 'F', an OIMap 'f' and an integer 'i'
-- OUTPUT: A BasisIndex made from F, f and i
-- COMMENT: i should be from 1 to #F.genWidths and f should be a map with source F.genWidths#(i - 1)
basisIndex = method(TypicalValue => BasisIndex)
basisIndex(FreeOIModule, OIMap, ZZ) := (F, f, i) -> (
    ret := new BasisIndex from {F, f, i};
    assertValid ret;
    ret
)

-- Validation method for BasisIndex
assertValid BasisIndex := b -> (
    if not #b == 3 then error("Expected list of length 3, instead got "|toString b);
    if not (instance(b#0, FreeOIModule) and instance(b#1, OIMap) and instance(b#2, ZZ)) then error("Expected list of the form {FreeOIModule, OIMap, ZZ}, instead got "|toString b);
    scan({b#0, b#1}, assertValid);

    freemod := b#0; oimap := b#1; i := b#2;
    if not (i <= #freemod.genWidths and i >= 1) then error("Expected i between 1 and #genWidths, instead got "|toString i);
    if not #(oimap#1) == freemod.genWidths#(i - 1) then error("Expected OIMap with source = genWidths#(i - 1), instead got "|toString oimap)
)

-- Define the new type OIMonomial
OIMonomial = new Type of List

-- PURPOSE: Make a new OIMonomial
-- INPUT: '(X, b)', a monomial 'X' in a PolynomialOIAlgebra and a BasisIndex 'b'
-- OUTPUT: An OIMonomial made from X and b
oiMonomial = method(TypicalValue => OIMonomial)
oiMonomial(RingElement, BasisIndex) := (X, b) -> (
    ret := new OIMonomial from {X, b};
    assertValid ret;
    ret
)

-- Shortcut version of oiMonomial
-- INPUT: '(X, F, f, i)', a monomial 'X', a FreeOIModule 'F', an OIMap 'f' and an index 'i' from 1 to #F.genWidths
oiMonomial(RingElement, FreeOIModule, OIMap, ZZ) := (X, F, f, i) -> oiMonomial(X, basisIndex(F, f, i))

-- Validation method for OIMonomial
assertValid OIMonomial := m -> (
    if not #m == 2 then error("Expected length 2 list for OIMonomial, instead got "|toString m);
    if not (instance(m#0, RingElement) and instance(m#1, BasisIndex)) then error("Expected list of the form {RingElement, BasisIndex}, instead got "|toString m);
    elt := m#0; b := m#1;

    assertValid b;
    freemod := b#0; oimap := b#1; wid := oimap#0;
    coeffs := ring getFreeModuleInWidth(freemod, wid, UpdateBasis => false); -- UpdateBasis => false avoids an infinite loop
    if not class elt === coeffs then error("Expected element of "|toString coeffs|", instead got "|toString elt|" which is an element of "|class elt);
    if not #(terms elt) == 1 then error("Expected a monomial, instead got "|toString elt);
    if not leadCoefficient elt == 1_(freemod.oiAlgebra.baseField) then error("Expected lead coefficient of 1, instead got "|toString(leadCoefficient elt))
)

-- Comparison method for OIMonomial
OIMonomial ? OIMonomial := (f, g) -> (
    scan({f, g}, assertValid);
    if f === g then return symbol ==;

    Xf := f#0; Xg := g#0; -- Get the monomials in the PolynomialOIAlgebra
    bf := f#1; bg := g#1; -- Get the BasisIndex objects
    oimapf := bf#1; oimapg := bg#1; -- Get the OIMaps
    indexf := bf#2; indexg := bg#2; -- Get the d_i

    if not bf#0 === bg#0 then return incomparable; -- Must belong to the same FreeOIModule
    freemod := bf#0;

    ord := freemod.monOrder#0;
    if ord === Lex then ( -- LEX ORDER
        vectf := prepend(oimapf#0, oimapf#1);
        vectg := prepend(oimapg#0, oimapg#1);

        if not indexf == indexg then if indexf < indexg then return symbol > else return symbol <;
        if not vectf == vectg then return vectf ? vectg; -- Here we may assume #vectf = #vectg since indexf = indexg
        use class Xf;
        return Xf ? Xg -- Use the lex order defined in the coefficient ring (see getAlgebraInWidth)
    )
    else if instance(ord, SchreyerMonomialOrder) then ( -- SCHREYER ORDER
        -- IMPLEMENT THIS
    )
    else error "Monomial order not supported"
)

--------------------------------------------------------------------------------
-- END: OIMonomial.m2 ----------------------------------------------------------
--------------------------------------------------------------------------------