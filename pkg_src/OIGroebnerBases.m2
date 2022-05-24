-- -*- coding: utf-8 -*-

-- PURPOSE: Algorithms for computing Gröbner bases, syzygies and free resolutions for submodules of free OI-modules over Noetherian polynomial OI-algebras
-- PROGRAMMER: Michael Morrow
-- LAST UPDATED: May 2022
-- COMMENT: This package was made using Macaulay2-Package-Template, available here: https://github.com/morrowmh/Macaulay2-Package-Template

newPackage("OIGroebnerBases",
    Headline => "Computation in OI-modules over Noetherian polynomial OI-algebras",
    Version => "0.1",
    Date => "April 4, 2022", -- Project birthday
    Keywords => { "Commutative Algebra" },
    Authors => {
        { Name => "Michael Morrow", HomePage => "https://michaelmorrow.org", Email => "michaelhmorrow98@gmail.com" }
    },
    DebuggingMode => true,
    HomePage => "https://github.com/morrowmh/OIGroebnerBases"
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
load "OIGroebnerBases.m2"
P = makePolynomialOIAlgebra(QQ,1,x);
F = makeFreeOIModule(P, e, {1});
installBasisElements(F, 1);
installBasisElements(F, 2);
installBasisElements(F, 3);

F_2; f = x_(1,2)*e_(2, {1}, 1) + x_(1,1)*e_(2, {2}, 1);
F_3; g = x_(1,3)*e_(3, {3}, 1) + x_(1,1)*e_(3, {1}, 1);

oiGB(Verbose => true, {f, g})

-- The above takes about 1 hour on my laptop
-- The below is a fast small example

F_1; f = x_(1,1)^2*e_(1, {1}, 1);
F_2; g = x_(1,2)^2*e_(2, {2}, 1) + x_(1,2)*x_(1,1)*e_(2, {2}, 1);
oiGB({f,g}, Verbose => true)