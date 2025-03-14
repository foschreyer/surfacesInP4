
chiI=method()
chiI(Number,Number,Number) := (m,d,sg) -> binomial(m+4,4)-(binomial(m+1,2)*d-m*(sg-1)+1)



chiITable=method()
chiITable(Number,Number) := (d,sg) -> apply(toList(-1..5),m->chiI(m,d,sg))


Ksquare=method()
-- H2+HK=2(sg-1)
-- d^2-10d-5HK-2K2+12x==0
Ksquare(Number,Number,Number) := (d,sg,x) -> (HK:=2*(sg-1)-d;
    floor(1/2*(d^2-10*d-5*HK+12*x)))

LeBarzN6=method()
LeBarzN6(Number,Number,Number) := (d,sg,x) -> (
    delta:=binomial(d-1,2)-sg;
    t:= binomial(d-1,3)-sg*(d-3)+2*(x-1);
    h:= floor(1/2*(delta*(delta-d+2)-3*t));
    floor(-1/144*d*(d-4)*(d-5)*(d^3+30*d^2-577*d+786)+
	    delta*(2*binomial(d,4)+2*binomial(d,3)-45*binomial(d,2)+148*d-317)-
	    1/2*binomial(delta,2)*(d^2-27*d+120)-2*binomial(delta,3)+
	    h*(delta-8*d+56)+t*(9*d-3*delta-28)+binomial(t,2))
    )

TEST ///
chiITable(9,6)
Ksquare(9,6,1)==-1
13^2-10*4^2==9
d=9,sg=6,x=1
LeBarzN6(9,6,1)==1
///
 

cubicScroll=method()
cubicScroll(Ring) := P4 -> minors(2,matrix{{P4_0,P4_1,P4_3},{P4_1,P4_2,P4_4}})

veroneseSurface=method()
veroneseSurface(Ring,Ring) := (P4,P2) -> (
    kk := coefficientRing P2;
    h:=basis(2,P2)*syz random(kk^1,kk^6); 
    X:=trim ker map(P2,P4,h);
    assert(degree X ==4 and dim X==3);
    X)

delPezzoSurface=method()
delPezzoSurface(Ring) := P4 -> ideal random(P4^1,P4^{2:-2})
delPezzoSurface(Ring,Ring) := (P4,P2) -> (
    kk:= coefficientRing P2;
    pts := {matrix{{1,0,0}},matrix{{0,1,0}},matrix{{0,0,1}},matrix{{1,1,1}},random(kk^1,kk^3)};
    pts2:= intersect apply(pts, pt-> ideal((vars P2)* (syz pt)));
    h:=gens truncate(3,pts2);
     X:=trim ker map(P2,P4,h);
    assert(degree X ==4 and dim X==3);
    X)


castelnouvoSurface=method()
castelnouvoSurface(Ring) := P4 -> minors(2,random(P4^{-2,2:-3},P4^{2:-4}))

bordigaSurface=method()
bordigaSurface(Ring) := P4 -> minors(3,random(P4^{4:-3},P4^{3:-4}))
bordigaSurface(Ring,Ring) := (P4,P2) -> (
    kk:= coefficientRing P2;
    pts := {matrix{{1,0,0}},matrix{{0,1,0}},matrix{{0,0,1}},matrix{{1,1,1}}}|apply(6,c->random(kk^1,kk^3));
    pts2:= intersect apply(pts, pt-> ideal((vars P2)* (syz pt)));
    h:=gens truncate(4,pts2);
    X:=trim ker map(P2,P4,h);
    assert(degree X ==6 and dim X==3);
    X)

OkonekIonescuSurface=method()
OkonekIonescuSurface(Ring,Ring) :=(P4,P2) -> (
    sixPoints:=apply(6,i->ideal random(P2^1,P2^{2:-1}));
    fivePoints:=apply(5,i->ideal random(P2^1,P2^{2:-1}));
    H:= intersect (apply(sixPoints,p->p^2)|fivePoints);
    X:= trim ker map(P2,P4,gens H);
    assert(dim X==3 and  degree X==7 and  (genera X)_1==4);
    X)



degree8OkonekSurface=method()
degree8OkonekSurface(Ring,Ring) :=(P4,E) -> (
    m6x2=random(E^6,E^{-2,-4});
    betti(T:=res(coker m6x2,LengthLimit=>3));
    X:= saturate ideal syz symExt(T.dd_3,P4);
    assert(dim X==3 and  degree X==8 and  (genera X)_1==6);
    X)

   
alexanderSurface=method()
alexanderSurface(Ring) := P4 -> (
    betti(L :=matrix{{P4_0,P4_1,P4_2}}|random(P4^1,P4^{15:-2}));
    betti(L2 :=map(P4^{3:-1},P4^{3:-1},0)|random(P4^{3:-1},P4^{15:-2}));
    betti (N:=transpose (transpose L| transpose L2));
    betti (fN:=res coker N);
    X:=trim ideal (fN.dd_4*syz fN.dd_4^{16..21});
    assert(dim X==3 and degree X==9 and (genera X)_1==6);
    X)


alexanderSurface(Ring,Ring) := (P4,P2) -> (
    --tenPts = minors(4,random(P4^5,P4^{4:-1}));
    --elapsedTime betti (h1=saturate (tenPts^4))
    betti(h1:=intersect apply(10,c->(ideal random(P2^1,P2^{2:-1}))^4));
    X:=trim ker map(P2,P4,(gens h1)_{0..4});
    assert(dim X==3 and degree X==9 and (genera X)_1==6);
    X)


specialityOneAlexanderSurface=method()
specialityOneAlexanderSurface(Ring,Ring) := (P4,E) -> (
    b1:=gens trim ideal(basis(2,E)%ideal(E_0,E_1))|matrix{{e_0,e_1}};
    bb:=b1||random(E^{1},source b1);
    T:=res(coker bb,LengthLimit=>3);
    X:=trim saturate ideal syz symExt(T.dd_3,P4);
    assert(dim X==3 and degree X== 9 and (genera X)_1==7);
    X)



degree10pi8RanestadSurface=method()
degree10pi8RanestadSurface(Ring) := P4 -> (
    a1:=transpose matrix apply (5,i->{x_i,random(0,P4)*P4_i});
    a2:=map(P4^1,P4^{2:-2},0)||matrix{{sum(3,i->random(0,P4)*P4_i^2),sum(2,i->random(0,P4)*P4_(i+3)^2)}};
    aa:=map(P4^2,,a1|a2);
    faa:=res(coker aa,LengthLimit=>4);
    b1:=faa.dd_3^{0..14}_{0..13};
    m15x5:=syz transpose syz (transpose (b1*random(source b1,P4^{1:-4})),DegreeLimit=>-3);
    X:= trim ideal(transpose (syz transpose (faa.dd_2_{0..14}*m15x5))_{2}*faa.dd_2);
    assert(dim X==3 and degree X==10 and (genera X)_1==8);
    X)

degree10pi9RanestadSurface=method()
degree10pi9RanestadSurface(Ring,Ring) := (P4,E) -> (
    a1:=(syz matrix{{E_0,E_1}})*random(E^{3:-1},E^{2:-2});
    a2:=map(E^2,,random(E^2,E^{2:-3})|transpose a1);
    T :=res(coker a2,LengthLimit=>4);
    X := saturate ideal syz symExt(T.dd_4,P4);
    assert(dim X ==3 and degree X==10 and (genera X)_1==9);
    X)

-*
degree10pi9RanestadSurface=method()
degree10pi9RanestadSurface(Ring,Ring) := P4 -> (
    N:=coker (matrix{{P4_0,P4_1,P4_2}}|gens (ideal(P4_3,P4_4))^2)
    betti(fN:=res N)
    a:=fN.dd_3^{3..13}_{1..15}
    m10x15:=transpose syz transpose syz ((random(P4^{2:-3},target a)*a),DegreeLimit=>4)
    a1:=m10x15*(fN.dd_4)^{1..15}
    syz a1
    k2:=map(P4^{5:-4},,koszul(2,vars P4))
    a2:=a1|(k2++k2)
    betti syz a2
*-

degree10DESSurface=method()
degree10DESSurface(Ring,Ring) := (P4,E) -> (
    bb:=random(E^2,E^{2:-2,-3});
    betti (T:= res(coker bb,LengthLimit=>3));
    X := saturate ideal syz symExt(T.dd_3,P4);
    assert(dim X ==3 and degree X==10 and (genera X)_1==9);
    X)


popescuSurface=method()

popescuSurface(Ring,Ring,Number):= (P4,E,s) -> (
    kk:= coefficientRing P4;
    aa:=if s==0 then map(E^1,E^{-2,2:-1},matrix{{E_0*E_1,E_3,E_4}}) else (
	if s==1 then map(E^1,E^{-2,2:-1},matrix{{ 0_E,E_3,E_4}})
	else map(E^1,E^{-2,2:-1},matrix{{ E_0*E_1,0,E_4}}));
    sa:=syz aa;
    bb:=sa*random(source sa,E^{3:-3});
    T := res(coker transpose bb,LengthLimit=>4);
    X := trim saturate ideal syz symExt(T.dd_4,P4);
    assert(dim X==3 and degree X==11 and (genera X)_1==11);
    X)
 


TEST ///
chiITable(4,1)
///
end

restart
load"smoothRationalSurfacesInP4.m2"
needsPackage("BGG")
kk=ZZ/nextPrime 10^3
P4=kk[x_0..x_4]
E=kk[e_0..e_4,SkewCommutative=>true]
P2=kk[t_0..t_2]

chiITable(11,11)
    
TEST ///
minimalBetti(X=cubicScroll(P4)),degree X
genX=genera X
assert(chiITable(degree X,genX_1)=={0, 0, 0, 3, 13, 35, 75})

minimalBetti(X=veroneseSurface(P4,P2)),degree X
genX=genera X
assert(chiITable(degree X,genX_1)=={0, 0, -1, 0, 7, 25, 60})


minimalBetti(X=delPezzoSurface(P4,P2)),degree X
genX=genera X
assert(chiITable(degree X,genX_1)=={-1, 0, 0, 2, 10, 29, 65})
minimalBetti(X=delPezzoSurface(P4)),degree X
genX=genera X
assert(chiITable(degree X,genX_1)=={-1, 0, 0, 2, 10, 29, 65})


minimalBetti(X=castelnouvoSurface(P4)),degree X
genX=genera X
assert(chiITable(degree X,genX_1)=={-2, 0, 0, 1, 7, 23, 55})

minimalBetti(X=bordigaSurface(P4)),degree X
genX=genera X
assert(chiITable(degree X,genX_1)=={-3, 0, 0, 0, 4, 17, 45})
minimalBetti(X=bordigaSurface(P4,P2)),degree X
genX=genera X
assert(chiITable(degree X,genX_1)=={-3, 0, 0, 0, 4, 17, 45})


elapsedTime  minimalBetti(X=alexanderSurface(P4))
degree X

elapsedTime minimalBetti(X=alexanderSurface(P4,P2))
degree X

elapsedTime minimalBetti(X=specialityOneAlexanderSurface(P4,E))
degree X

elapsedTime minimalBetti(X=degree10pi8RanestadSurface(P4)) 
degree X

elapsedTime minimalBetti(X=degree10pi9RanestadSurface(P4,E))
degree X

elapsedTime minimalBetti(X=degree10DESSurface(P4,E))
degree X

minimalBetti(X=popescuSurface(P4,E,0))
singX=X+minors(2,jacobian X);
dim singX == 0

minimalBetti(X=popescuSurface(P4,E,1))
degree X
X5=ideal (gens X)_{0..9};
R=X5:X;
dim R, degree R, minimalBetti R
singX=X+minors(2,jacobian X);
dim singX == 0


minimalBetti(X=popescuSurface(P4,E,2))
X5=ideal (gens X)_{0..9};
R=X5:X;
dim R, degree R, minimalBetti R, degree (R+X)
cRX=primaryDecomposition (R+X)
apply(cRX,c-> (dim c, degree c, betti c))
last cRX
betti(fX=res X)
fX.dd_4
singX=X+minors(2,jacobian X);
dim singX == 0




///


--%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%




TEST//
chiITable(12,12)
Ksquare(12,12,1)
LeBarzN6(12,12,1)
(7+9)*2-3*5

betti(b=map(P4^15,,(koszul(2,vars P4)++koszul(2,vars P4)++koszul(2,vars P4))*random(kk^30,kk^18)))
betti syz(b,DegreeLimit=>2)
minimalBetti coker random(P4^5,P4^{18:-1})
minimalBetti coker random(P4^1,P4^{8:-2})
betti res coker  random(E^7,E^{5:-1})
betti syz random(E^3,E^{5:-2})


chiITable(13,14),chiITable(13,15)
Ksquare(13,14,1)
LeBarzN6(13,15,1)
(12+9)*2-25

chiITable(14,14),chiITable(14,18)
Ksquare(14,18,1)
LeBarzN6(14,18,1)
(16+9)*2-7*5

///
