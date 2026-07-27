needsPackage"NongeneralTypeSurfacesInP4"
kk=ZZ/nextPrime 10^4;P4=kk[x_0..x_4];E=kk[e_0..e_4,SkewCommutative=>true];
-*
(degree, sectionalGenus, number of points blownup, s=h^1(O_X(1)), genus of polarization)
candidatesWithGenus={
    (7, 5, 1, 0, 5),
    (8, 6, 1, 0, 7),
    (9, 8, 5, 1, 8),
    (10, 9, 3, 1, 15),
    (11, 11, 5, 2, 21),
    (11, 11, 5, 2, 18),
    (11, 11, 5, 2, 16),
    (11, 11, 5, 2, 15),
    (11, 12, 10, 3, 13),
    (12, 14, 11, 4, 20)}
*-
-- computations for the (11, 11, 5, 2, 21) example:
setRandomSeed("fix decomposition of D");

minimalBetti(X=K3surfaceD11S11Ln(P4,0))

D=canonicalDivisor X;
selfIntersectionNumber(X,D)
elapsedTime tally apply(cD=decompose D,c->(dim c, degree c, genus c))
(d,sg) =(degree X, sectionalGenus X)
HdotK(d,sg)==9
Ksquare(d,sg,2)==-5
R5=residualInQuintics X; degree R5, dim R5
--tally apply(primaryDecomposition(R5+X),c-> (dim c, degree c, genus c))
LeBarzN6(d,sg,2)==4
pd={1,1,1,1,5}
polarizationDegree=d+sum(pd,k->k^2)
polGenus=sub((polarizationDegree+2)/2,ZZ)
elapsedTime D=canonicalDivisor X;
betti D

netList apply(cD,c->(dim c, degree c, genus c))


betti(sD3=saturate(X+cD_3^5))
degree sD3
betti (D1=intersect(sD3,cD_0,cD_1,cD_2))
matrix apply(cD,c->apply(cD,d-> dim(c+d)))
betti(H7=ideal(gens D1*random(source gens D1,P4^{-7})))
betti(residual=(X+H7):D1)
degree residual
betti (res1=trim ideal((gens residual)%X))
betti (H8=trim ideal( (gens intersect((ideal vars P4)^8,res1))%X))
betti(h8a=gens trim ideal (((gens H8)_{0..21})%(X+H7)))
betti (h8b=map(P4^1,,vars P4*H7_0))
P21=kk[y_0..y_21]
elapsedTime betti(Y=trim ker map(P4/X,P21, h8b|h8a))

dim Y, degree Y, genera Y

L4=ideal(y_0..y_4)
betti(pts1=saturate (L4+Y))
degree pts1, dim pts1
elapsedTime pts=apply(cD,c->(elapsedTime p=trim ker map(P4/c,P21, h8b|h8a);
	<< betti p <<endl;p));
netList apply(pts_{0,1,3}, p-> transpose syz transpose sub(jacobian p,kk)	)
pts_2
elapsedTime betti (p3=saturate((pts_3)^5+Y))
elapsedTime betti(pts1a=(pts1:pts_2))
elapsedTime betti(pts1b=((pts1a:pts_1):pts_0))
degree pts1, degree pts1a, degree pts1b

A2=kk[w,z]
betti(m5=(ideal vars A2)^5)
m5a=ideal(gens m5*random(source gens m5,A2^{5:-5}));
degree m5a, degree m5
