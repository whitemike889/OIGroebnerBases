-- -*- coding: utf-8 -*-

-- PURPOSE: Algorithms for computing Gröbner bases, syzygies and free resolutions for submodules of free OI-modules over Noetherian polynomial OI-algebras
-- PROGRAMMER: Michael Morrow
-- LAST UPDATED: July 2022
-- FIRST OFFICIAL RELEASE: 7/10/2022
-- COMMENT: This package was made using Macaulay2-Package-Template, available here: https://github.com/morrowmh/Macaulay2-Package-Template

newPackage("OIGroebnerBases",
    Headline => "Computation in OI-modules over Noetherian polynomial OI-algebras",
    Version => "1.0.2",
    Date => "April 4, 2022", -- Project birthday
    Keywords => { "Commutative Algebra" },
    Authors => {
        { Name => "Michael Morrow", HomePage => "https://michaelmorrow.org", Email => "michaelhmorrow98@gmail.com" }
    },
    DebuggingMode => false,
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

load "OIResolution.m2"

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

-- Scratch work 

load "OIGroebnerBases.m2"
P = makePolynomialOIAlgebra(QQ,1,x);
F = makeFreeOIModule(P, e, {1,2});
installBasisElements(F, 1);
installBasisElements(F, 2);
F_1; b1 = x_(1,1)*e_(1,{1},1);
F_2; b2 = x_(1,2)^2*e_(2,{1,2},2); b3 = e_(2,{2},1);
oiRes({b1,b2,b3}, 2, Verbose => true)

restart
load "OIGroebnerBases.m2"
P = makePolynomialOIAlgebra(QQ,1,x);
F = makeFreeOIModule(P, e, {1});
installBasisElements(F, 1);
installBasisElements(F, 2);
installBasisElements(F, 3);
installBasisElements(F, 4);

-- Res example 1
F_1; b1 = x_(1,1)*e_(1,{1},1); b2 = x_(1,1)^2*e_(1,{1},1);
F_2; b3 = x_(1,2)*e_(2,{1},1);
C = oiRes({b1, b2, b3}, 1, Verbose => true)

-- Res example 2
F_1; b1 = x_(1,1)*e_(1,{1},1);
F_2; b2 = x_(1,2)*e_(2,{1},1);
C = oiRes({b1,b2}, 0, Verbose => true)

-- Syzygy example 1
F_1; b1 = x_(1,1)^3*e_(1,{1},1);
F_2; b2 = x_(1,1)^2*e_(2,{1},1); b3 = x_(1,2)^2*e_(2,{2},1); b4 = x_(1,1)*x_(1,2)*e_(2,{2},1);
B = oiGB({b1, b2, b3, b4}, Verbose => true)
C = oiSyz(B, d, Verbose => true)
isOIGB C

-- Syzygy example 2
F_1; f = x_(1,1)^3*e_(1,{1}, 1);
F_2; h = x_(1,2)^2*e_(2, {2}, 1) + x_(1,1)*x_(1,2)*e_(2, {2}, 1);
B = oiGB({f, h}, Verbose => true)
C = oiSyz(B, d, Verbose => true)
isOIGB C

-- Syzygy example 3
F_1; f = x_(1,1)^3*e_(1,{1}, 1);
F_2; h = x_(1,2)^2*e_(2, {2}, 1) + x_(1,1)*x_(1,2)*e_(2, {2}, 1);
F_3; g = x_(1,3)*e_(3, {2}, 1);
B = oiGB({f, g, h}, Verbose => true)
C = oiSyz(B, d, Verbose => true)
isOIGB C