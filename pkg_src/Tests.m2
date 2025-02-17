-- Test 0: Compute a Groebner basis
TEST ///
P = makePolynomialOIAlgebra(QQ,1,x);
F = makeFreeOIModule(P, e, {1});
installBasisElements(F, 1);
installBasisElements(F, 2);
installBasisElements(F, 3);

F_1; f = x_(1,1)^3*e_(1,{1}, 1);
F_2; h = x_(1,2)^2*e_(2, {2}, 1) + x_(1,1)*x_(1,2)*e_(2, {2}, 1);
B = oiGB {f, h};

F_2; elt1 = x_(1,2)*x_(1,1)^2*e_(2,{2},1);
F_3; elt2 = (-x_(1,3)*x_(1,2)+x_(1,3)*x_(1,1))*e_(3,{3},1);

checkB = apply(B, makeMonic);
checkSet = apply({f, h, elt1, elt2}, makeMonic);
assert(set checkB === set checkSet)
///

-- Test 1: Compute first syzygies
TEST ///
P = makePolynomialOIAlgebra(QQ,1,x);
F = makeFreeOIModule(P, e, {1});
installBasisElements(F, 1);
installBasisElements(F, 2);

F_1; b1 = x_(1,1)^3*e_(1,{1},1);
F_2; b2 = x_(1,1)^2*e_(2,{1},1); b3 = x_(1,2)^2*e_(2,{2},1); b4 = x_(1,1)*x_(1,2)*e_(2,{2},1);
B = oiGB {b1, b2, b3, b4};
C = oiSyz(B, d);

G = freeOIModuleFromElement C#0;
installBasisElements(G, 2);
installBasisElements(G, 3);

G_2;
width2stuff = {
d_(2,{1},1)-x_(1,1)*d_(2,{1,2},2),
x_(1,1)*d_(2,{1,2},3)-x_(1,2)*d_(2,{1,2},4),
d_(2,{2},1)-x_(1,2)*d_(2,{1,2},3)
};

G_3;
width3stuff = {
-d_(3,{1,3},2)+d_(3,{1,2},2),
d_(3,{2,3},2)-d_(3,{1,2},3),
x_(1,1)*d_(3,{2,3},4)-x_(1,2)*d_(3,{1,3},4),
-d_(3,{2,3},3)+d_(3,{1,3},3),
x_(1,2)*d_(3,{1,3},3)-x_(1,3)*d_(3,{2,3},4)
};

checkC = apply(C, makeMonic);
checkSet = apply(join(width2stuff, width3stuff), makeMonic);
assert(set checkC === set checkSet)
///

-- Test 2: Compute length 1 resolution
TEST ///
P = makePolynomialOIAlgebra(QQ,1,x);
F = makeFreeOIModule(P, e, {1});
installBasisElements(F, 1);
installBasisElements(F, 2);
F_1; b1 = x_(1,1)*e_(1,{1},1); b2 = x_(1,1)^2*e_(1,{1},1);
F_2; b3 = x_(1,2)*e_(2,{1},1);
C = oiRes({b1, b2, b3}, 1, MinimalOIGB => false);
assert isComplex C;
assert(getGenWidths C_1 == {2,2,3,3});
assert(getDegShifts C_1 == {-2,-3,-2,-2})
///