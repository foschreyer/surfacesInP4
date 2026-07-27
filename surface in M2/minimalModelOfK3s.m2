needsPackage"NongeneralTypeSurfacesInP4"
kk=ZZ/nextPrime 10^4;P4=kk[x_0..x_4];E=kk[e_0..e_4,SkewCommutative=>true];


minimalBetti(X=K3surfaceD11S11Ln(P4,0))
D=canonicalDivisor X;
selfIntersectionNumber(X,D)
tally apply(decompose D,c->(dim c, degree c, genus c))
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
cD=decompose D;
netList apply(cD,c->(dim c, degree c, genus c))


betti(sD2=saturate(X+cD_2^5))
degree sD2
betti (D1=intersect(sD2,cD_0,cD_1))
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
