--------------------------------------------------------------------------------
-- BEGIN: SchreyerMonomialOrder.m2 ---------------------------------------------
--------------------------------------------------------------------------------

-- Define the new type SchreyerMonomialOrder
SchreyerMonomialOrder = new Type of HashTable

-- Install net method for SchreyerMonomialOrder

-- PURPOSE: Check if a given SchreyerMonomialOrder is valid
-- INPUT: A SchreyerMonomialOrder 'S'
-- OUTPUT: Nothing if S is a valid SchreyerMonomialOrder, otherwise error
assertValid SchreyerMonomialOrder := S -> (
    if not sort keys S === sort {srcMod, targMod, schreyerList} then error("Invalid SchreyerMonomialOrder HashTable keys: "|toString keys S);
    if not instance(S.srcMod, FreeOIModule) or not instance(S.targMod, FreeOIModule) then error("Expected type FreeOIModule for srcMod and targMod, instead got types "|toString class S.srcMod|" and "|toString class S.targMod);
    if S.srcMod === S.targMod then error "srcMod cannot equal targMod";
    scan({S.srcMod, S.targMod}, assertValid);
    
    if not instance(S.schreyerList, List) or #S.schreyerList == 0 then error("Expected nonempty List for schreyerList, instead got "|toString S.schreyerList);
    for i to #S.schreyerList - 1 do (
        elt := S.schreyerList#i;
        wid := widthOfElement elt;
        par := freeOIModuleFromElement elt;
        if not class elt === getFreeModuleInWidth(par, wid) then error("Element "|toString i|" of schreyerList does not belong to its specified parent OI-module in width "|toString wid);
        if not wid == (S.srcMod).genWidths#i then error("Element "|toString i|" of schreyerList has width "|toString wid|" which does not match srcMod.genWidths#i = "|toString (S.srcMod).genWidths#i)
    )
)

-- PURPOSE: Make a new SchreyerMonomialOrder
-- INPUT: '(targModArg, srcModArg, schreyerListArg)', a FreeOIModule 'targModArg', a FreeOIModule 'srcModArg' and a nonempty List 'schreyerListArg' of elements of targModArg
-- OUTPUT: A SchreyerMonomialOrder made from targModArg, srcModArg and schreyerListArg
-- COMMENT: Error if targModArg === srcModArg
schreyerMonomialOrder = method(TypicalValue => SchreyerMonomialOrder)
schreyerMonomialOrder(FreeOIModule, FreeOIModule, List) := (targModArg, srcModArg, schreyerListArg) -> (
    if targModArg === srcModArg then error "srcMod cannot equal targMod";
    if #schreyerListArg == 0 then error "Expected nonempty List for schreyerList";
    
    ret := new SchreyerMonomialOrder from {targMod => targModArg, srcMod => srcModArg, schreyerList => schreyerListArg};
    assertValid ret;
    ret
)

-- PURPOSE: Install a SchreyerMonomialOrder on its source module
-- INPUT: A SchreyerMonomialOrder 'S'
-- OUTPUT: If S is a valid SchreyerMonomialOrder, sets (S.srcMod).monOrder#0 to S
installSchreyerMonomialOrder = method()
installSchreyerMonomialOrder SchreyerMonomialOrder := S -> (
    assertValid S;
    (S.srcMod).monOrder#0 = S
)

-- Shortcut version
installSchreyerMonomialOrder(FreeOIModule, FreeOIModule, List) := (targModArg, srcModArg, schreyerListArg) -> (
    S := schreyerMonomialOrder(targModArg, srcModArg, schreyerListArg);
    (S.srcMod).monOrder#0 = S
)

--------------------------------------------------------------------------------
-- END: SchreyerMonomialOrder.m2 -----------------------------------------------
--------------------------------------------------------------------------------