-- -*- coding: utf-8 -*-

-- PURPOSE: Algorithms for computing Gröbner bases, syzygies and free resolutions for submodules of free OI-modules over Noetherian polynomial OI-algebras
-- PROGRAMMER: Michael Morrow
-- LAST UPDATED: May 2022
-- COMMENT: This package was made using Macaulay2-Package-Template, available here: https://github.com/morrowmh/Macaulay2-Package-Template

newPackage("OIModules",
    Headline => "Computation in OI-modules over Noetherian polynomial OI-algebras",
    Version => "0.1",
    Date => "April 4, 2022", -- Project birthday
    Keywords => { "Commutative Algebra" },
    Authors => {
        { Name => "Michael Morrow", HomePage => "https://michaelmorrow.org", Email => "michaelhmorrow98@gmail.com" }
    },
    DebuggingMode => true,
    HomePage => "https://github.com/morrowmh/OIModules"
)

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- EXPORT AND PROTECT ----------------------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

load "ExportAndProtect.m2"

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- BODY ------------------------------------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

load "OIMap.m2"

load "PolynomialOIAlgebra.m2"

load "FreeOIModule.m2"

load "InducedModuleMap.m2"

load "Algorithms.m2"

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- DOCUMENTATION ---------------------------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

beginDocumentation()

load "Documentation.m2"

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- TESTS -----------------------------------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

load "Tests.m2"

end

-- Scratch work section

restart
load "OIModules.m2"
P = makePolynomialOIAlgebra(QQ, 1, x);
F = makeFreeOIModule(P, e, {2,3});
installBasisElements(F, 5);
F_5;
f = x_(1,5)^2*e_(5, {2,3}, 1) + x_(1,3)^2*e_(5, {1,3,4}, 2);
installBasisElements(F, 6);
F_6;
g = x_(1,6)*e_(6, {1, 6}, 1) + x_(1,2)*e_(6, {2,4,6}, 2);
G = makeFreeOIModule(P, d, {5, 6}, DegreeShifts => {-2, -1});
phi = makeFreeOIModuleMap(F, G, {f, g});
installBasisElements(G, 7);
G_7;
h = x_(1,7)^2*x_(1,6)*d_(7, {1, 3, 4, 5, 7}, 1) + x_(1,5)^3*d_(7, {1, 4, 5, 6, 7}, 1);
installSchreyerMonomialOrder phi;
assert(leadOITerm h === (getOITermsFromVector(x_(1,5)^3*d_(7, {1, 4, 5, 6, 7}, 1)))#0);
isHomogeneous phi