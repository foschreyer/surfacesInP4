

chinH=method()
chinH(Number,Number,Number) := (m,d,sg) -> (binomial(m+1,2)*d-m*(sg-1)+1)
chiI=method()
chiI(Number,Number,Number) := (m,d,sg) -> binomial(m+4,4)-chinH(m,d,sg)


apply(toList(-1..7),n->chiI(n,12,13))

kk=ZZ/11
P4=kk[x_0..x_4]

prepareAboSurfaces=method()
prepareAboSurface(Ring) := P4 -> (
    kk=coefficientRing P4
    needsPackage("BGG")
    E=kk[e_0..e_4,SkewCommutative=>true]
    m2x3=matrix{{e_0,e_1,e_3},{e_1,e_2,e_4}}-- random(E^2,E^{3:-1})
    bs=flatten apply(4,i->flatten apply(2,j->apply(10,k->b_(i,j,k))))
    as=flatten apply(2,i->flatten apply(3,j->apply(10,k->a_(i,j,k))))
    B=kk[bs,as]
    ExB=E**B
    E2=sub(basis(2,E),ExB)
    b4x2=matrix apply(4,i->apply(2,j->sum(10,k->(b_(i,j,k)*E2_(0,k)))))
    a2x3=matrix apply(2,i->apply(3,j->sum(10,k->(a_(i,j,k)*E2_(0,k)))))
    E3=sub(basis(3,E),ExB)
)
n=117
AboSurface=method()
AboSurface(Number,Number) := (n,k) -> (
    assert(member(n,toList(113..117)));
    assert(n+k <121);
    count=1;test=1;
    while(
    while(
    while(
    m2xk=map(kk^2,kk^0,0);
    scan(k,c-> (
	    while (m2x2=random(kk^2,kk^2); det m2x2==0) do ();
	    m2xk=m2xk|m2x2*m2x3*random(kk^3,kk^1)));
    m4x2=map(E^4,,transpose (m2xk|random(E^2,E^{4-k:-1})));
    c=b4x2*sub(m2x3,ExB)+sub(m4x2,ExB)*a2x3;
    I=trim ideal sub(contract(E3,flatten c),B);
    numgens I =!= n) do (count=count+1);
    sol=vars B%I;
    randSol=sub(sol,random(kk^1,kk^140));
    b4x2r=sub(b4x2,vars E|randSol);
    betti(bb=map(E^4,,m4x2|b4x2r));
    test1 = degrees source syz bb =={{3}, {3}, {3}, {4}, {4}, {4}, {4}, {4}};
    test2 = degrees source syz transpose bb=={{2}, {2}, {2}, {2}, {2}, {2}, {2}, {2}, {2}, {2}, {2}, {2}, {2}};
    not(test1 and test2) ) do (test=test+1;count=count+1);
    betti(T=res(coker bb, LengthLimit=>4));
    X=saturate ideal syz symExt(T.dd_4,P4);
    not (dim X ==3 and degree X==12) ) do ();
    <<count <<endl;
    <<test <<endl;
    X)
elapsedTime X=AboSurface(113,4);
count,test
minimalBetti X, betti res coker transpose bb
log(char kk,count)
X5=ideal(gens X)_{0..4};
dim X5, degree X5, genera X, genera X5
R=X5:X
dim R, degree R, minimalBetti R
radical R==R
apply(decompose R,c->(dim c, degree c, degree (c+X), dim (c+X)))

smoothAboSurface=method()
smoothAboSurface(Number,Number) := (n,k) -> (
    assert(member(n,toList(113..117)));
    assert(n+k <121);
    countSmooth=1;
    while (
	elapsedTime X=AboSurface(n,k);
	singX=X+minors(2,jacobian X);
	dim singX !=0 ) do (countSmooth=countSmooth+1);
    <<countSmooth;
    X)

elapsedTime X=smoothAboSurface(113,4); 
countSmooth
minimalBetti X, betti res coker transpose bb
X5=ideal(gens X)_{0..4};
dim X5, degree X5, genera X, genera X5
R=X5:X
dim R, degree R, minimalBetti R
radical R==R
primaryDecomposition R
apply(decompose R,c->(dim c, degree c, degree (c+X), dim (c+X), minimalBetti c))
genus R
minimalBetti X
betti(fX=res(X, FastNonminimal=>true))
betti(omegaX=Ext^1(X,P4^{-5}))
minimalBetti omegaX
P12=kk[y_0..y_12]
P4xP12=P4**P12
graph=sub(vars P12,P4xP12)*sub(presentation omegaX,P4xP12);
pL=sub(diff(sub(transpose vars P4,P4xP12),graph),P12);
elapsedTime Y= ann coker pL;
dim Y, degree Y, genera Y
minimalBetti Y
while(
Hs=apply(3,c->random(kk^1,kk^5));
dim(X+sum(Hs,h->ideal(vars P4*transpose h))) !=0) do()
betti(excLines=saturate sum(Hs,h->ann coker map(P12^4,,transpose syz h*pL)))
dim excLines,degree excLines,degree R
degree excLines+degree R==8
minimalBetti X, degree R, degree excLines
-*
               0  1  2  3 4
o419 = (total: 1 10 19 13 3, 4, 4)
            0: 1  .  .  . .
            1: .  .  .  . .
            2: .  .  .  . .
            3: .  .  .  . .
            4: .  5  1  . .
            5: .  5 18 13 3
*-
