-- -*- coding: utf-8 -*-

newPackage("OIModules",
    Headline => "Computation in OI-modules over Noetherian OI-algebras",
    Version => "0.1",
    Date => "April 4, 2022",
    Authors => {
        { Name => "Michael Morrow", HomePage => "https://michaelmorrow.org", Email => "michaelhmorrow98@gmail.com" }
    },
    DebuggingMode => true,
    HomePage => "https://github.com/morrowmh/OIModules"
)

--------------------------------------------------------------------------------
-- EXPORTS
--------------------------------------------------------------------------------

load "Exports.m2"

--------------------------------------------------------------------------------
-- BODY
--------------------------------------------------------------------------------



--------------------------------------------------------------------------------
-- DOCUMENTATION
--------------------------------------------------------------------------------

beginDocumentation()

load "Documentation.m2"

--------------------------------------------------------------------------------
-- TESTS
--------------------------------------------------------------------------------

load "Tests.m2"

end