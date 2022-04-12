load "OI.m2"

--------------------------------------------------------------------------------
-- FROM: PolynomialOIAlgebras.m2 -----------------------------------------------
--------------------------------------------------------------------------------

-- Define the new type PolynomialOIAlgebra
PolynomialOIAlgebra = new Type of HashTable
net PolynomialOIAlgebra := P -> (
    "Base field: "|net(P#"baseField") ||
    "Number of variable rows: "|net(P#"varRows") ||
    "Generated in width: "|net(P#"genWidth")
)

-- PURPOSE: Check if a given PolynomialOIAlgebra object is valid
-- INPUT: A PolynomialOIAlgebra 'P'
-- OUTPUT: Nothing if P is a valid PolynomialOIAlgebra object, otherwise error
validatePolynomialOIAlgebra = method()
validatePolynomialOIAlgebra PolynomialOIAlgebra := P -> (
    if not sort keys P == sort {"baseField", "varRows", "genWidth"} then error "Invalid PolynomialOIAlgebra HashTable keys";
    if not instance(P#"baseField", Ring) or not isField P#"baseField" then error("Expected a field, not "|toString(P#"baseField"));
    if not instance(P#"varRows", ZZ) or P#"varRows" < 1 then error("Expected a positive integer row count, not "|toString(P#"varRows"));
    if not instance(P#"genWidth", ZZ) or not (P#"genWidth" == 0 or P#"genWidth" == 1) then error("Expected generator width of either 0 or 1, not "|toString(P#"genWidth"))
)

-- PURPOSE: Check if a given width is valid
-- INPUT: An integer 'n'
-- OUTPUT: Nothing if n is a valid width, otherwise error
validateWidth = method()
validateWidth ZZ := n -> (
    if n < 0 then error("Expected nonnegative width, not "|toString(n))
)

-- PURPOSE: Make a new PolynomialOIAlgebra
-- INPUT: '(K, c, d)', a field of coefficients 'K', a positive integer 'c' of rows and a generator width 'd' of either 0 or 1
-- OUTPUT: A PolynomialOIAlgebra made from K, c, d
polynomialOIAlgebra = method(TypicalValue => PolynomialOIAlgebra)
polynomialOIAlgebra(Ring, ZZ, ZZ) := (K, c, d) -> (
    P := new PolynomialOIAlgebra from {"baseField" => K, "varRows" => c, "genWidth" => d};
    validatePolynomialOIAlgebra P;
    P
)

-- PURPOSE: Get the variables from a PolynomialOIAlgebra in a specified width
-- INPUT: '(P, n)', a PolynomialOIAlgebra 'P' and a width 'n'
-- OUTPUT: A list of columns of variables for P_n, the width n algebra of P
-- COMMENT: The variables are grouped by column and ordered so that in P_n we have x_(i,j)>x_(i',j') iff j>j' or j=j' and i>i'
getVariablesInWidth = method(TypicalValue => List)
getVariablesInWidth(PolynomialOIAlgebra, ZZ) := (P, n) -> (
    validatePolynomialOIAlgebra P;
    validateWidth n;
    if P#"genWidth" == 0 or n == 0 then return {};

    -- Generate variables in the desired order
    x := symbol x;
    variables := new MutableList from {};
    for j from 1 to n do (
        column := new MutableList from {};

        for i to P#"varRows" - 1 do ( 
            column#i = x_(P#"varRows" - i, j)
        );

        variables#(n - j) = toList(column)
    );

    toList(variables)
)

-- PURPOSE: Get the algebra from a PolynomialOIAlgebra in a specified width
-- INPUT: '(P, n)', a PolynomialOIAlgebra 'P' and a width 'n'
-- OUTPUT: P_n, the width n algebra of P
-- COMMENT: We use the "position down over term" monomial order and the standard ZZ-grading
getAlgebraInWidth = method(TypicalValue => PolynomialRing)
getAlgebraInWidth(PolynomialOIAlgebra, ZZ) := (P, n) -> (
    validatePolynomialOIAlgebra P;
    validateWidth n;
    if P#"genWidth" == 0 or n == 0 then return P#"baseField";

    variables := getVariablesInWidth(P, n);
    P#"baseField"[flatten variables, Degrees => {#variables:1}, MonomialOrder => {Position => Down, Lex}]
)

-- PURPOSE: Get the maps between two algebras in a PolynomialOIAlgebra
-- INPUT: '(P, m, n)', a PolynomialOIAlgebra 'P', a width 'm' and a width 'n' with m ≤ n
-- OUTPUT: A list of the (OI-induced) algebra maps between P_m and P_n, i.e. P(Hom(m, n))
-- COMMENT: Returns an empty list if n < m and returns the identity map if either genWidth=0 or m=0
getAlgebraMapsBetweenWidths = method(TypicalValue => List)
getAlgebraMapsBetweenWidths(PolynomialOIAlgebra, ZZ, ZZ) := (P, m, n) -> (
    validatePolynomialOIAlgebra P;
    validateWidth m; validateWidth n;
    if n < m then return {};
    if P#"genWidth" == 0 or m == 0 then return {map(getAlgebraInWidth(P, n), P#"baseField")};

    algMaps := new MutableList from {};
    oiMaps := getOIMaps(m, n);
    targ := getAlgebraInWidth(P, n);
    src := getAlgebraInWidth(P, m);
    use src;

    -- Generate algebra maps
    for oiMap in oiMaps do (
        variables := getVariablesInWidth(P, m);

        -- TODO: Complete this section

        algMaps = append(algMaps, map(targ, src))
    );

    toList(algMaps)
)