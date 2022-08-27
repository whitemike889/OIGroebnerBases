export {
    -- Types
    "OIMap",
    "PolynomialOIAlgebra",

    -- Keys
    "ColUpRowUp", "ColUpRowDown", "ColDownRowUp", "ColDownRowDown", "RowUpColUp", "RowUpColDown", "RowDownColUp", "RowDownColDown",

    -- Methods
    "makeOIMap", "getOIMaps", "composeOIMaps",
    "makePolynomialOIAlgebra", "getAlgebraInWidth", "getInducedAlgebraMap",

    -- Options
    "VariableOrder"
}

scan({
    -- Keys
    targWidth, img,
    baseField, varRows, varSym, varOrder, algebras, maps
}, protect)