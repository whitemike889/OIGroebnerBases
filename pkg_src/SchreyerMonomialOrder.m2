--------------------------------------------------------------------------------
-- BEGIN: SchreyerMonomialOrder.m2 ---------------------------------------------
--------------------------------------------------------------------------------

-- Define the new type SchreyerMonomialOrder
-- COMMENT: Should be of the form {srcMod => FreeOIModule, targMod => FreeOIModule, schreyerList => List}
SchreyerMonomialOrder = new Type of HashTable
SchreyerMonomialOrder.synonym = "Schreyer monomial order"

-- Install net method for SchreyerMonomialOrder
net SchreyerMonomialOrder := S -> "<<Schreyer monomial order>>"||
    "Source module: "|toString S.srcMod ||
    "Target module: "|toString S.targMod ||
    "Schreyer list: "|net S.schreyerList

-- Verification method for SchreyerMonomialOrder
verifyData SchreyerMonomialOrder := S -> (
    if not sort keys S === sort {srcMod, targMod, schreyerList} then error("Expected keys {srcMod, targMod, schreyerList}, instead got "|toString keys S);
    if not instance(S.srcMod, FreeOIModule) or not instance(S.targMod, FreeOIModule) then error("Expected type FreeOIModule for srcMod and targMod, instead got types "|toString class S.srcMod|" and "|toString class S.targMod);
    if S.srcMod === S.targMod then error "srcMod cannot equal targMod";
    scan({S.srcMod, S.targMod}, verifyData);
    
    if not instance(S.schreyerList, List) or #S.schreyerList == 0 then error("Expected nonempty List for schreyerList, instead got "|toString S.schreyerList);
    for i to #S.schreyerList - 1 do (
        elt := S.schreyerList#i;
        if not instance(elt, Vector) then error("Expected a Vector, instead got "|toString elt);
        verifyData elt;
        
        if not (class elt).Width == S.srcMod.genWidths#i then error("Element "|toString i|" of schreyerList has width "|toString (class elt).Width|" which does not match srcMod.genWidths#"|toString i|" = "|toString S.srcMod.genWidths#i)
    )
)

-- PURPOSE: Make a new SchreyerMonomialOrder
-- INPUT: '(G, F, L)', a FreeOIModule 'G', a FreeOIModule 'F' and a  List 'L' of elements of G
-- OUTPUT: A SchreyerMonomialOrder made from G, F and L
makeSchreyerMonomialOrder = method(TypicalValue => SchreyerMonomialOrder, Options => {VerifyData => true})
makeSchreyerMonomialOrder(FreeOIModule, FreeOIModule, List) := opts -> (G, F, L) -> (
    ret := new SchreyerMonomialOrder from {targMod => G, srcMod => F, schreyerList => L};
    if opts.VerifyData then verifyData ret;
    ret
)

-- PURPOSE: Install a SchreyerMonomialOrder on its source FreeOIModule
-- INPUT: A SchreyerMonomialOrder 'S'
installSchreyerMonomialOrder = method(Options => {VerifyData => true})
installSchreyerMonomialOrder SchreyerMonomialOrder := opts -> S -> (
    if opts.VerifyData then verifyData S;
    S.srcMod.monOrder#0 = S;
)

--------------------------------------------------------------------------------
-- END: SchreyerMonomialOrder.m2 -----------------------------------------------
--------------------------------------------------------------------------------