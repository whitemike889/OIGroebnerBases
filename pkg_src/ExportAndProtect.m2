export {
    -- Types
    "OIMap",
    "PolynomialOIAlgebra",

    -- Methods
    "makeOIMap", "getOIMaps", "composeOIMaps",
    "makePolynomialOIAlgebra", "getAlgebraInWidth", "getInducedAlgebraMap"
}

scan({
    -- Keys
    targWidth, img,
    baseField, varRows, varSym, varOrder, algebras, maps
}, protect)