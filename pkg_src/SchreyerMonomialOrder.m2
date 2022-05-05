--------------------------------------------------------------------------------
-- BEGIN: SchreyerMonomialOrder.m2 ---------------------------------------------
--------------------------------------------------------------------------------

-- Define the new type SchreyerMonomialOrder
-- COMMENT: Should be of the form {srcMod => FreeOIModule, targMod => FreeOIModule, schreyerList => List}
SchreyerMonomialOrder = new Type of HashTable

-- Install net method for SchreyerMonomialOrder

-- Validation method for SchreyerMonomialOrder
assertValid SchreyerMonomialOrder := S -> (
    if not sort keys S === sort {srcMod, targMod, schreyerList} then error("Expected keys {srcMod, targMod, schreyerList}, instead got "|toString keys S);
    if not instance(S.srcMod, FreeOIModule) or not instance(S.targMod, FreeOIModule) then error("Expected type FreeOIModule for srcMod and targMod, instead got types "|toString class S.srcMod|" and "|toString class S.targMod);
    if S.srcMod === S.targMod then error "srcMod cannot equal targMod";
    scan({S.srcMod, S.targMod}, assertValid);
    
    if not instance(S.schreyerList, List) or #S.schreyerList == 0 then error("Expected nonempty List for schreyerList, instead got "|toString S.schreyerList);
    for i to #S.schreyerList - 1 do (
        elt := S.schreyerList#i;
        if not instance(elt, Vector) then error("Expected a Vector, instead got "|toString elt);

        Width := widthOfElement elt;
        freeOIMod := freeOIModuleFromElement elt;

        if not class elt === getFreeModuleInWidth(freeOIMod, Width, UpdateBasis => false) then error("Element "|toString i|" of schreyerList does not belong to its specified free OI-module in width "|toString Width);
        if not Width == S.srcMod.genWidths#i then error("Element "|toString i|" of schreyerList has width "|toString Width|" which does not match srcMod.genWidths#"|toString i|" = "|toString S.srcMod.genWidths#i)
    )
)

-- PURPOSE: Make a new SchreyerMonomialOrder
-- INPUT: '(G, F, L)', a FreeOIModule 'G', a FreeOIModule 'F' and a  List 'L' of elements of G
-- OUTPUT: A SchreyerMonomialOrder made from G, F and L
makeSchreyerMonomialOrder = method(TypicalValue => SchreyerMonomialOrder, Options => {AssertValid => true})
makeSchreyerMonomialOrder(FreeOIModule, FreeOIModule, List) := opts -> (G, F, L) -> (
    ret := new SchreyerMonomialOrder from {targMod => G, srcMod => F, schreyerList => L};
    if opts.AssertValid then assertValid ret;
    ret
)

-- PURPOSE: Install a SchreyerMonomialOrder on its source module
-- INPUT: A SchreyerMonomialOrder 'S'
-- OUTPUT: If S is a valid SchreyerMonomialOrder, sets S.srcMod.monOrder#0 to S
installSchreyerMonomialOrder = method(Options => {AssertValid => true})
installSchreyerMonomialOrder SchreyerMonomialOrder := opts -> S -> (
    if opts.AssertValid then assertValid S;
    S.srcMod.monOrder#0 = S
)

--------------------------------------------------------------------------------
-- END: SchreyerMonomialOrder.m2 -----------------------------------------------
--------------------------------------------------------------------------------