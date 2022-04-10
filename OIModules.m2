-- -*- coding: utf-8 -*-

-- PURPOSE: Algorithms for computing Gröbner bases, syzygies and free resolutions for submodules of free OI-modules over Noetherian polynomial OI-algebras
-- PROGRAMMER: Michael Morrow (https://michaelmorrow.org)
-- LAST UPDATED: April 2022

newPackage("OIModules",
    Headline => "Computation in OI-modules over Noetherian OI-algebras",
    Version => "0.1",
    Date => "April 4, 2022",
    Keywords => {"Commutative Algebra"},
    Authors => {
        { Name => "Michael Morrow", HomePage => "https://michaelmorrow.org", Email => "michaelhmorrow98@gmail.com" }
    },
    DebuggingMode => true,
    HomePage => "https://github.com/morrowmh/OIModules"
)

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- EXPORTS ---------------------------------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

export {
    "PolynomialOIAlgebra",
    "polynomialOIAlgebra",
    "validatePolynomialOIAlgebra",
    "validateWidth",
    "getRingFromWidth"
}

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- BODY ------------------------------------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

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
-- OUTPUT: Nothing if 'P' is a valid PolynomialOIAlgebra object, otherwise error
validatePolynomialOIAlgebra = method()
validatePolynomialOIAlgebra PolynomialOIAlgebra := P -> (
    if not sort keys P == sort {"baseField", "varRows", "genWidth"} then error "Invalid PolynomialOIAlgebra keys";
    if not instance(P#"baseField", Ring) or not isField P#"baseField" then error("Expected a field, not "|toString(P#"baseField"));
    if not instance(P#"varRows", ZZ) or P#"varRows" < 1 then error("Expected a positive integer row count, not "|toString(P#"varRows"));
    if not instance(P#"genWidth", ZZ) or not (P#"genWidth" == 0 or P#"genWidth" == 1) then error("Expected either d = 0 or d = 1, not d = "|toString(P#"genWidth"))
)

-- PURPOSE: Check if a given width is valid
-- INPUT: An integer 'n'
-- OUTPUT: Nothing if 'n' is a valid width, otherwise error
validateWidth = method()
validateWidth ZZ := n -> (
    if n < 0 then error("Expected nonnegative width, not "|toString(n))
)

-- PURPOSE: Make a new PolynomialOIAlgebra
-- INPUT: '(K, c, d)', a field of coefficients 'K', a positive integer 'c' of rows and a generator width 'd' of either 0 or 1
-- OUTPUT: A PolynomialOIAlgebra
polynomialOIAlgebra = method(TypicalValue => PolynomialOIAlgebra)
polynomialOIAlgebra(Ring, ZZ, ZZ) := (K, c, d) -> (
    P := new PolynomialOIAlgebra from {"baseField" => K, "varRows" => c, "genWidth" => d};
    validatePolynomialOIAlgebra P;
    P
)

-- PURPOSE: Get ring from PolynomialOIAlgebra in width n
-- INPUT: '(P, n)', a PolynomialOIAlgebra 'P' and a nonnegative width 'n'
-- OUTPUT: The width 'n' polynomial ring of 'P'
getRingFromWidth = method(TypicalValue => PolynomialRing)
getRingFromWidth(PolynomialOIAlgebra, ZZ) := (P, n) -> (
    validatePolynomialOIAlgebra P;
    validateWidth n;
    if P#"genWidth" == 0 or n == 0 then return P#"baseField";
    
    x = symbol x;
    variables := new MutableList from {};
    for j from 0 to n - 1 do (
        for i from 0 to P#"varRows" - 1 do (
            variables#(i * n + j) = x_(n - j, P#"varRows" - i)
        )
    );

    P#"baseField"[variables, Degrees => {#variables:1}, MonomialOrder => {Position => Down, Lex}]
)

--------------------------------------------------------------------------------
-- FROM: FreeOIModules.m2 ------------------------------------------------------
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- DOCUMENTATION ---------------------------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

beginDocumentation()

doc ///
Node
    Key
        OIModules
    Headline
        Computation in OI-modules over Noetherian polynomial OI-algebras
    Description
        Text
            This package allows one to compute Gröbner bases, syzygies and free resolutions for submodules of free OI-modules over Noetherian polynomial OI-algebras.
///

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- TESTS -----------------------------------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------



end