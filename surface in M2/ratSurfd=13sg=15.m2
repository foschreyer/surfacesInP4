restart
loadPackage ("NongeneralTypeSurfacesInP4")
d=13,sg=15
 chiITable(d,sg)
apply(toList(-5..7),i-> chiI(i,d,sg))
 LeBarzN6(d,sg,1)
 Ksquare(d,sg,1)

kk=ZZ/101
P4=kk[x_0..x_4]
E=kk[e_0..e_4,SkewCommutative=>true]
E2=basis(2,E)
E3=basis(3,E)
m5x3=matrix apply(5,i-> apply(3,j->E_((i+j)%5)))--+E_((i-j)%5)))
    m5x2=random(E^0,E^{2:-1})
scan(5,i->(m5x2=m5x2||(m5x3^{i}*random(kk^3,kk^2))))
m5x2
AB=kk[a_(0,0,0)..a_(2,4,9),b_(0,0,0)..b_(4,1,9)]
EAB=E**AB
A=matrix apply(3,i->apply(5,j->sum(10,k->sub(a_(i,j,k),EAB)*sub(E2_(0,k),EAB))))
B=matrix apply(5,i->apply(2,j->sum(10,k->sub(b_(i,j,k),EAB)*sub(E2_(0,k),EAB))))
m2x5=map(E^{2:-2},,transpose m5x2)
m2x5=random(E^{2:-2},E^{5:-3})

rel:=method()
rel(Matrix,Matrix) := (m5x3,m2x5) -> trim ideal sub(contract(sub(E3,EAB),sub(m5x3,EAB)*A+B*sub(m2x5,EAB)),AB)
betti(J=rel(m5x3,m2x5))
redAB=vars AB%J;
#support redAB

sol=sub(redAB,random(kk^1,kk^250));
sol
Br=map(E^5,E^{2:-2},sub(B,vars E|sol));
betti res coker (m5x3|Br)
betti res coker transpose (m5x3|Br)
Ar=map(E^{3:0},E^{5:-2},sub(A,vars E|sol))
betti Ar
	betti (m2x5**E^{1}||Ar)
	betti res coker transpose (m2x5**E^{1}||Ar)
betti (T=res coker (m2x5**E^{1}||Ar))
minimalBetti (X=ideal syz symExt(T.dd_3,P4))
betti(fX=res X)
betti(omega1=Ext^2(module X, P4^{-5}))
degree omega1, dim omega1
nCMlocus =ann omega1
minimalBetti nCMlocus

singX= saturate( X+minors(2,jacobian X));
dim singX, degree singX
csingX=decompose singX
tally apply(csingX,c->(dim c, degree c, minimalBetti c))
intersect select(csingX,c->dim c==1)==nCMlocus
betti T
degree X, dim X, genera X
