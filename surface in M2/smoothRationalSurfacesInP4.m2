
sectionalGenus= X -> (genera X)_1

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
chiITable(13,15)
Ksquare(13,15,1)
LeBarzN6(13,15,1)
2*(9+12)-8
///
 

cubicScroll=method()
cubicScroll(PolynomialRing) := P4 -> minors(2,matrix{{P4_0,P4_1,P4_3},{P4_1,P4_2,P4_4}})

veroneseSurface=method()
veroneseSurface(PolynomialRing,PolynomialRing) := (P4,P2) -> (
    kk := coefficientRing P2;
    h:=basis(2,P2)*syz random(kk^1,kk^6); 
    X:=trim ker map(P2,P4,h);
    assert(degree X ==4 and dim X==3);
    X)

delPezzoSurface=method()
delPezzoSurface(PolynomialRing) := P4 -> ideal random(P4^1,P4^{2:-2})
delPezzoSurface(PolynomialRing,PolynomialRing) := (P4,P2) -> (
    kk:= coefficientRing P2;
    pts := {matrix{{1,0,0}},matrix{{0,1,0}},matrix{{0,0,1}},matrix{{1,1,1}},random(kk^1,kk^3)};
    pts2:= intersect apply(pts, pt-> ideal((vars P2)* (syz pt)));
    h:=gens truncate(3,pts2);
     X:=trim ker map(P2,P4,h);
    assert(degree X ==4 and dim X==3);
    X)


castelnouvoSurface=method()
castelnouvoSurface(PolynomialRing) := P4 -> minors(2,random(P4^{-2,2:-3},P4^{2:-4}))

bordigaSurface=method()
bordigaSurface(PolynomialRing) := P4 -> minors(3,random(P4^{4:-3},P4^{3:-4}))
bordigaSurface(PolynomialRing,PolynomialRing) := (P4,P2) -> (
    kk:= coefficientRing P2;
    pts := {matrix{{1,0,0}},matrix{{0,1,0}},matrix{{0,0,1}},matrix{{1,1,1}}}|apply(6,c->random(kk^1,kk^3));
    pts2:= intersect apply(pts, pt-> ideal((vars P2)* (syz pt)));
    h:=gens truncate(4,pts2);
    X:=trim ker map(P2,P4,h);
    assert(degree X ==6 and dim X==3);
    X)

ionescuOkonekSurface=method()
ionescuOkonekSurface(PolynomialRing,PolynomialRing) :=(P4,P2) -> (
    sixPoints:=apply(6,i->ideal random(P2^1,P2^{2:-1}));
    fivePoints:=apply(5,i->ideal random(P2^1,P2^{2:-1}));
    H:= intersect (apply(sixPoints,p->p^2)|fivePoints);
    X:= trim ker map(P2,P4,gens H);
    assert(dim X==3 and  degree X==7 and  (genera X)_1==4);
    X)



degree8OkonekSurface=method()
degree8OkonekSurface(PolynomialRing,Ring) :=(P4,E) -> (
    m6x2=random(E^6,E^{-2,-4});
    betti(T:=res(coker m6x2,LengthLimit=>3));
    X:= saturate ideal syz symExt(T.dd_3,P4);
    assert(dim X==3 and  degree X==8 and  (genera X)_1==6);
    X)

degree8AlexanderSurface=method()
degree8AlexanderSurface(PolynomialRing,PolynomialRing) := (P4,P2) -> (
    H:= intersect (apply(10,i->(ideal random(P2^1,P2^{2:-1}))^2)|{ideal random(P2^1,P2^{2:-1})});
    X:= trim ker map(P2,P4,gens H);
    assert(dim X==3 and degree X==8 and (genera X)_1==5);
    X)


nonspecialAlexanderSurface=method()
nonspecialAlexanderSurface(PolynomialRing) := P4 -> (
    betti(L :=matrix{{P4_0,P4_1,P4_2}}|random(P4^1,P4^{15:-2}));
    betti(L2 :=map(P4^{3:-1},P4^{3:-1},0)|random(P4^{3:-1},P4^{15:-2}));
    betti (N:=transpose (transpose L| transpose L2));
    betti (fN:=res coker N);
    X:=trim ideal (fN.dd_4*syz fN.dd_4^{16..21});
    assert(dim X==3 and degree X==9 and (genera X)_1==6);
    X)


nonspecialAlexanderSurface(PolynomialRing,PolynomialRing) := (P4,P2) -> (
    --tenPts = minors(4,random(P4^5,P4^{4:-1}));
    --elapsedTime betti (h1=saturate (tenPts^4))
    betti(h1:=intersect apply(10,c->(ideal random(P2^1,P2^{2:-1}))^4));
    X:=trim ker map(P2,P4,(gens h1)_{0..4});
    assert(dim X==3 and degree X==9 and (genera X)_1==6);
    X)


specialityOneAlexanderSurface=method()
specialityOneAlexanderSurface(PolynomialRing,Ring) := (P4,E) -> (
    b1:=gens trim ideal(basis(2,E)%ideal(E_0,E_1))|matrix{{E_0,E_1}};
    bb:=b1||random(E^{1},source b1);
    T:=res(coker bb,LengthLimit=>3);
    X:=trim saturate ideal syz symExt(T.dd_3,P4);
    assert(dim X==3 and degree X== 9 and (genera X)_1==7);
    X)



degree10pi8RanestadSurface=method()
degree10pi8RanestadSurface(PolynomialRing) := P4 -> (
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
degree10pi9RanestadSurface(PolynomialRing,Ring) := (P4,E) -> (
    a1:=(syz matrix{{E_0,E_1}})*random(E^{3:-1},E^{2:-2});
    a2:=map(E^2,,random(E^2,E^{2:-3})|transpose a1);
    T :=res(coker a2,LengthLimit=>4);
    X := saturate ideal syz symExt(T.dd_4,P4);
    assert(dim X ==3 and degree X==10 and (genera X)_1==9);
    X)


degree10DESSurface=method()
degree10DESSurface(PolynomialRing,Ring) := (P4,E) -> (
    bb:=random(E^2,E^{2:-2,-3});
    betti (T:= res(coker bb,LengthLimit=>3));
    X := saturate ideal syz symExt(T.dd_3,P4);
    assert(dim X ==3 and degree X==10 and (genera X)_1==9);
    X)


popescuSurface=method()

popescuSurface(Ring,Ring,Number):= (P4,E,s) -> (
    kk:= coefficientRing P4;
    if not member(s,{0,1,2}) then error "expect s in {0,1,2}";
	aa:=null;
    if s==0 then aa=map(E^1,E^{-2,2:-1},matrix{{E_0*E_1,E_3,E_4}});
    if s==1 then aa=map(E^1,E^{-2,2:-1},matrix{{ 0_E,E_3,E_4}}); 
    if s==2 then aa=map(E^1,E^{-2,2:-1},matrix{{ E_0*E_1,0,E_4}});
    sa:=syz aa;
    bb:=sa*random(source sa,E^{3:-3});
    T := res(coker transpose bb,LengthLimit=>4);
    X := trim saturate ideal syz symExt(T.dd_4,P4);
    assert(dim X==3 and degree X==11 and (genera X)_1==11);
    X)

vBELSurface=method()
vBELSurface(Ring,Ring) := (P4,P2) -> (
    if char P4 !=2 then error "expect a ground field of caharcteristic 2";
    if char P2 =!= char P4 then error "P2 and P4 should have the same characteristic 2";
    t:= symbol t;
    FF14:=ZZ/2[t]/ideal(t^14+t^13+t^11+t^10+t^8+t^6+t^4+t+1);
    P2FF14:=FF14[gens P2];
    Q:=ideal(vars P2FF14*syz matrix{{t^11898,t^137, 1}});
    FF5:=ZZ/2[t]/ideal(t^5 +t^3 +t^2 +t +1);
    P2FF5:=FF5[gens P2];
    R:=ideal(vars P2FF5*syz matrix{{t^6 ,t^15, 1}});
    Q14:=ker map(P2FF14/Q,P2);
    R5:=ker map(P2FF5/R,P2);
    P:=ideal(P2_0,P2_1);
    H:=intersect(saturate(Q14^2),R5,P^3);
    X:=ker map(P2,P4,(gens H)_{0..4});
    assert(dim(X+minors(2, jacobian X))==0);
    X)
x3
---------------------------------------
--      Abo-Ranestad surfaces        --
---------------------------------------

prepareAboRanestadSurfaces=method()
prepareAboRanestadSurfaces(Ring) := P4 -> (
    kk:=coefficientRing P4;
    E:=kk[e_0..e_4,SkewCommutative=>true];
    m2x3:=matrix{{e_0,e_1,e_3},{e_1,e_2,e_4}};-- random(E^2,E^{3:-1})
    bs:=flatten apply(4,i->flatten apply(2,j->apply(10,k->b_(i,j,k))));
    as:=flatten apply(2,i->flatten apply(3,j->apply(10,k->a_(i,j,k))));
    B:=kk[bs,as];
    ExB:=E**B;
    E2:=sub(basis(2,E),ExB);
    b4x2:=matrix apply(4,i->apply(2,j->sum(10,k->(sub(b_(i,j,k),ExB)*E2_(0,k)))));
    a2x3:=matrix apply(2,i->apply(3,j->sum(10,k->(sub(a_(i,j,k),ExB)*E2_(0,k)))));
    E3:=sub(basis(3,E),ExB);
(E,m2x3,bs,as,B,ExB,E2,b4x2,a2x3,E3))

AboRanestadSurface=method()
AboRanestadSurface(Ring,Number) := (P4,n) -> (
    -- Input: P4 ring of P4
    --        n number of desired generators of the ideal I below, 
    -- Output: X an ideal of an AR surface,
    --         m4x2 linear matrix over the exterior algebra    
    assert(member(n,toList(112..117)));
    k:=min(4,120-n);
    kk:= coefficientRing P4;
    (E,m2x3,bs,as,B,ExB,E2,b4x2,a2x3,E3):=prepareAboRanestadSurfaces(P4);
    count:=1;test:=1;
    m2xk:= null; m2x2:=null;I:=null;sol:=null;randSol:=null;
    b4x2r:=null;bb:=null;test1:=null;test2:=null;T:=null;X:=null;
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
    (X,m4x2))

AboRanestadSurface(Ring,Number,Number) := (P4,n,b) -> (
    -- Input: P4 ring of P4
    --        n number of desired generators of the ideal I below, 
    --        b number of generators of the desired surface (b=9 or 10 in the examples)
    -- Output: X an ideal of an AR surface,
    --         m4x2 a linear matrix over the exterior algebra     
    assert(member(n,toList(112..117)));
    k:=min(4,120-n);
    kk:= coefficientRing P4;
    (E,m2x3,bs,as,B,ExB,E2,b4x2,a2x3,E3):=prepareAboRanestadSurfaces(P4);
    count:=1;test:=1;
    m2xk:= null; m2x2:=null;I:=null;sol:=null;randSol:=null;
    b4x2r:=null;bb:=null;test1:=null;test2:=null;T:=null;X:=null;
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
    not ( numgens X == b and dim X ==3 and degree X==12) ) do ();
    X5:=ideal (gens X)_{0..4};
    R:=X5:X;
    << (degree R, dim R) <<endl;
    << minimalBetti X <<endl;
    <<count <<endl;
    <<test <<endl;
    (X,m4x2))



smoothAboRanestadSurface=method()
smoothAboRanestadSurface(Ring,Number) := (P4,n) -> (
    assert(member(n,toList(112..117)));
    countSmooth:=1;singX:=null;X:=null;m4x2:=null;m2x3:=null;
    while (
	elapsedTime (X,m4x2)=AboRanestadSurface(P4,n);
	singX=X+minors(2,jacobian X);
	dim singX !=0 ) do (countSmooth=countSmooth+1);
    <<countSmooth;
    (X,m4x2))

smoothAboRanestadSurface(Ring,Number,Number) := (P4,n,b) -> (
    assert(member(n,toList(112..117)));
    countSmooth:=1;singX:=null;X:=null;
    while (
	elapsedTime (X,m4x2)=AboRanestadSurface(P4,n,b);
	singX=X+minors(2,jacobian X);
	dim singX !=0 ) do (countSmooth=countSmooth+1);
    <<countSmooth;
    (X,m4x2))

collectSmoothAboRanestadSurfaces=method()
collectSmoothAboRanestadSurfaces(Ring,Number,Number) :=(P4,n,N) -> (
    m4x2s:={};Xs:={};adjTypes:={};
    X:=null;m4x2:=null;m2x3:=null;numList:=null;L1:=null;L2:=null;J:=null;
    count:=0;
    scan(N, i-> (
	    elapsedTime (X,m4x2)=smoothAboRanestadSurface(P4,n);
	    elapsedTime (numList,L1,L2,J)=adjunctionProcess(X,4);
	    Xs=append(Xs,X);
	    adjTypes=append(adjTypes,numList);
	    m4x2s=append(m4x2s,m4x2)));
    return (Xs,adjTypes,m4x2s))

smoothAboRanestadSurfaceFromMatrix=method()
smoothAboRanestadSurfaceFromMatrix(Matrix) := m4x2 -> (
    E:=ring m4x2;
    kk:=coefficientRing E;
    x:= symbol x;
    P4:=kk[x_0..x_4];
    m2x3:=matrix{{E_0,E_1,E_3},{E_1,E_2,E_4}};-- random(E^2,E^{3:-1})
    bs:=flatten apply(4,i->flatten apply(2,j->apply(10,k->b_(i,j,k))));
    as:=flatten apply(2,i->flatten apply(3,j->apply(10,k->a_(i,j,k))));
    B:=kk[bs,as];
    ExB:=E**B;
    E2:=sub(basis(2,E),ExB);
    b4x2:=matrix apply(4,i->apply(2,j->sum(10,k->(sub(b_(i,j,k),ExB)*E2_(0,k)))));
    a2x3:=matrix apply(2,i->apply(3,j->sum(10,k->(sub(a_(i,j,k),ExB)*E2_(0,k)))));
    E3:=sub(basis(3,E),ExB);
    c:=b4x2*sub(m2x3,ExB)+sub(m4x2,ExB)*a2x3;
    I:=trim ideal sub(contract(E3,flatten c),B);
    <<numgens I<<endl;
    sol:=vars B%I;
    test1:=null;test2:=null;b4xr:=null;bb:=null;T:=null;X:=null;singX:=null;
    test:=1;count:=1;randSol:=null;
    elapsedTime while (
	while (randSol=sub(sol,random(kk^1,kk^140));
	    b4x2r=sub(b4x2,vars E|randSol);
	    betti(bb=map(E^4,,m4x2|b4x2r));
	    test1 = degrees source syz bb =={{3}, {3}, {3}, {4}, {4}, {4}, {4}, {4}};
	    test2 = degrees source syz transpose bb=={{2}, {2}, {2}, {2}, {2}, {2}, {2}, {2}, {2}, {2}, {2}, {2}, {2}};
	not(test1 and test2) ) do (test=test+1;count=count+1);
        betti(T=res(coker bb, LengthLimit=>4));
	X=saturate ideal syz symExt(T.dd_4,P4);
	singX=X+minors(2,jacobian X);
    not (dim singX == 0 and dim X ==3 and degree X==12) ) do ();
    X)

///
setRandomSeed("more adjunction types A")
P4=ZZ/7[x_0..x_4]
elapsedTime (Xs,adjTypes,m4x2s)=collectSmoothAboRanestadSurfaces(P4,113,8);

tally apply(Xs,X->minimalBetti X)
tally adjTypes
-*
Tally{{(4, 12, 13), 4, (12, 24, 13), 12, (12, 16, 5), 0, (4, 4, 1)} => 4}
      {(4, 12, 13), 8, (12, 24, 13), 1, (12, 20, 9), 8, (8, 9, 2)} => 4
*-
P4=ZZ/nextPrime 10^3[x_0..x_4]
elapsedTime (Xs,adjTypes,m4x2s)=collectSmoothAboRanestadSurfaces(P4,116,1);
m4x2=first m4x2s
minimalBetti(X=smoothAboRanestadSurfaceFromMatrix m4x2)
///

/// -- example (v)
E=ZZ/3[e_0..e_4,SkewCommutative=>true]
m4x2=map(E^4,,transpose matrix{{-e_4,-e_2-e_3+e_4,-e_1,e_0-e_1-e_2+e_3+e_4},
            {-e_2-e_3+e_4,e_0+e_1+e_2+e_3-e_4,e_2,-e_1-e_2+e_3-e_4}})
minimalBetti(X=smoothAboRanestadSurfaceFromMatrix m4x2)
elapsedTime (numList,L1,L2,J)=adjunctionProcess(X,3);
numList, 
-*
{(4, 12, 13), 8, (12, 24, 13), 1, (12, 20, 9), 8, (8, 9, 2)}
*-
minimalBetti J
-*
             0  1  2  3  4  5 6
o13 = total: 1 19 58 75 44 11 2
          0: 1  .  .  .  .  . .
          1: . 19 58 75 44  5 .
          2: .  .  .  .  .  6 2

*-
///



---------------------------------
--       schreyer surfaces     --
---------------------------------

findRandomSchreyerSurface=method()
findRandomSchreyerSurface(Ring) := P4 -> (
    F:=res(ideal vars P4, LengthLimit=>3);
    kk:=coefficientRing P4;
    M:=nil;fM:=nil;N:=nil;N1:=nil;
    while(
    while(
      while (
	while (M=ideal (F.dd_3*random(F_3,P4^{-4}));
          apply(4,i->hilbertFunction(i,M))!={1,5,5,0}) do ();
	fM=res(M,DegreeLimit=>1,LengthLimit=>3);
	rank fM_3 <2) do ();
        while (
	    N1=random(P4^{rank fM_3:-4},P4^{2:-4});
	  coker transpose N1 !=0) do ();
      N = coker transpose (fM.dd_3*N1);
      (dim N , degree N)!=(0,2)) do ();
    J1:=syz transpose (fM.dd_2*syz transpose syz(transpose(fM.dd_3*N1),DegreeLimit=>-3));
    source J1 != P4^{0,-2}) do ();
    trim ideal(transpose J1_{1}*syz(fM.dd_1))
    )

findRandomSchreyerSurface(Ring,Number) := (P4,s) -> (
    F:=res(ideal vars P4, LengthLimit=>3);
    kk:=coefficientRing P4;
    M:=nil;fM:=nil;N:=nil;N1:=nil;
    while(
    while(
      while (
	while (M=ideal (F.dd_3*random(F_3,P4^{-4}));
          apply(4,i->hilbertFunction(i,M))!={1,5,5,0}) do ();
	fM=res(M,DegreeLimit=>1,LengthLimit=>3);
	rank fM_3 <s) do ();
        while (
	    N1=random(P4^{rank fM_3:-4},P4^{2:-4});
	  coker transpose N1 !=0) do ();
      N = coker transpose (fM.dd_3*N1);
      (dim N , degree N)!=(0,2)) do ();
    J1:=syz transpose (fM.dd_2*syz transpose syz(transpose(fM.dd_3*N1),DegreeLimit=>-3));
    source J1 != P4^{0,-2}) do ();
    trim ideal(transpose J1_{1}*syz(fM.dd_1))
    )

singSchreyerSurfacesStatistic=method()

singSchreyerSurfacesStatistic(Ring,Number) := (P4,N) -> (
    Ms:={};L:={};X:=null;M:=null;Rdata:=null;
    count:=0;
    while (
	elapsedTime X=findRandomSchreyerSurface(P4);
	M= moduleFromSchreyerSurface(X);
	Ms=append(Ms,M);
	X5=ideal (gens X)_{0..4};
	R=X5:X;
	hypX:=X+ideal jacobian X;
	singX:=X+minors(2,jacobian X);
	elapsedTime Rdata=(minimalBetti M, dim R, degree R, minimalBetti R,
	    dim singX, degree singX, dim (R+singX));
	<<Rdata<<endl;
	L=append(L,Rdata);
	count=count+1;
	count<N) do ();
    --<<tally L <<endl;
    L)
/// -- some experimental values
needsPackage"BGG"
loadPackage "AdjunctionForSurfaces"
load"smoothRationalSurfacesInP4.m2"

P4=(ZZ/3)[x_0..x_4]
elapsedTime L7=singSchreyerSurfacesStatistic(P4,3^7);  -- 20455.8 seconds elapsed
(3^7,20455.8/60/60) -- (2187 examples, 5.68217 hours)
tally sort apply(L7,data->data_{1,2,4})
-*
Tally{{2, 5, 0} => 18 }
            {2, 5, 1} => 46
            {2, 5, 2} => 163
            {2, 5, 3} => 17
            {2, 6, 0} => 29
            {2, 6, 1} => 53
            {2, 6, 2} => 213
            {2, 6, 3} => 38
            {2, 7, 0} => 12
            {2, 7, 1} => 78
            {2, 7, 2} => 136
            {2, 7, 3} => 16
            {2, 8, 2} => 33
            {2, 8, 3} => 21
            {3, 1, 0} => 3
            {3, 1, 1} => 46
            {3, 1, 2} => 186
            {3, 1, 3} => 14
            {3, 2, 0} => 2
            {3, 2, 1} => 22
            {3, 2, 2} => 850
            {3, 2, 3} => 110
            {3, 3, 1} => 3
            {3, 3, 2} => 23
            {3, 3, 3} => 22
            {3, 4, 2} => 13
            {3, 4, 3} => 1
            {3, 5, 2} => 11
            {3, 5, 3} => 6
            {4, 1, 3} => 2
*-
Lsm=select(L7,data->data_4==0);(#L7,#Lsm)==(2187, 64)
tally sort apply(Lsm,data->data_{0,1,2})
-*
                    0  1  2  3  4 5
o88 = Tally{{total: 1 10 22 28 20 5, 2, 5} => 18}
                 0: 1  .  .  .  . .
                 1: . 10 15  2  . .
                 2: .  .  7 26 20 5
                    0  1  2  3  4 5
            {total: 1 10 22 28 20 5, 2, 6} => 29
                 0: 1  .  .  .  . .
                 1: . 10 15  2  . .
                 2: .  .  7 26 20 5
                    0  1  2  3  4 5
            {total: 1 10 22 28 20 5, 2, 7} => 12
                 0: 1  .  .  .  . .
                 1: . 10 15  2  . .
                 2: .  .  7 26 20 5
                    0  1  2  3  4 5
            {total: 1 10 22 28 20 5, 3, 1} => 2
                 0: 1  .  .  .  . .
                 1: . 10 15  2  . .
                 2: .  .  7 26 20 5
                    0  1  2  3  4 5
            {total: 1 10 23 29 20 5, 3, 1} => 1
                 0: 1  .  .  .  . .
                 1: . 10 15  3  . .
                 2: .  .  8 26 20 5
                    0  1  2  3  4 5
            {total: 1 10 23 29 20 5, 3, 2} => 2
                 0: 1  .  .  .  . .
                 1: . 10 15  3  . .
                 2: .  .  8 26 20 5

*-
tally sort apply(L7,data->data_{0,1,2})
-*
                    0  1  2  3  4 5
o92 = Tally{{total: 1 10 22 28 20 5, 2, 5} => 244}
                 0: 1  .  .  .  . .
                 1: . 10 15  2  . .
                 2: .  .  7 26 20 5
                    0  1  2  3  4 5
            {total: 1 10 22 28 20 5, 2, 6} => 333
                 0: 1  .  .  .  . .
                 1: . 10 15  2  . .
                 2: .  .  7 26 20 5
                    0  1  2  3  4 5
            {total: 1 10 22 28 20 5, 2, 7} => 231
                 0: 1  .  .  .  . .
                 1: . 10 15  2  . .
                 2: .  .  7 26 20 5
                    0  1  2  3  4 5
            {total: 1 10 22 28 20 5, 3, 1} => 218
                 0: 1  .  .  .  . .
                 1: . 10 15  2  . .
                 2: .  .  7 26 20 5
                    0  1  2  3  4 5
            {total: 1 10 22 28 20 5, 3, 2} => 822
                 0: 1  .  .  .  . .
                 1: . 10 15  2  . .
                 2: .  .  7 26 20 5
                    0  1  2  3  4 5
            {total: 1 10 22 28 20 5, 3, 3} => 1
                 0: 1  .  .  .  . .
                 1: . 10 15  2  . .
                 2: .  .  7 26 20 5
                    0  1  2  3  4 5
            {total: 1 10 23 29 20 5, 2, 7} => 11
                 0: 1  .  .  .  . .
                 1: . 10 15  3  . .
                 2: .  .  8 26 20 5
                    0  1  2  3  4 5
            {total: 1 10 23 29 20 5, 2, 8} => 54
                 0: 1  .  .  .  . .
                 1: . 10 15  3  . .
                 2: .  .  8 26 20 5
                    0  1  2  3  4 5
            {total: 1 10 23 29 20 5, 3, 1} => 31
                 0: 1  .  .  .  . .
                 1: . 10 15  3  . .
                 2: .  .  8 26 20 5
                    0  1  2  3  4 5
            {total: 1 10 23 29 20 5, 3, 2} => 144
                 0: 1  .  .  .  . .
                 1: . 10 15  3  . .
                 2: .  .  8 26 20 5
                    0  1  2  3  4 5
            {total: 1 10 23 29 20 5, 3, 3} => 25
                 0: 1  .  .  .  . .
                 1: . 10 15  3  . .
                 2: .  .  8 26 20 5
                    0  1  2  3  4 5
            {total: 1 10 24 30 20 5, 3, 2} => 18
                 0: 1  .  .  .  . .
                 1: . 10 15  4  . .
                 2: .  .  9 26 20 5
                    0  1  2  3  4 5
            {total: 1 10 24 30 20 5, 3, 3} => 22
                 0: 1  .  .  .  . .
                 1: . 10 15  4  . .
                 2: .  .  9 26 20 5
                    0  1  2  3  4 5
            {total: 1 10 24 30 20 5, 3, 4} => 8
                 0: 1  .  .  .  . .
                 1: . 10 15  4  . .
                 2: .  .  9 26 20 5
                    0  1  2  3  4 5
            {total: 1 10 25 31 20 5, 3, 4} => 6
                 0: 1  .  .  .  . .
                 1: . 10 15  5  . .
                 2: .  . 10 26 20 5
                    0  1  2  3  4 5
            {total: 1 10 25 31 20 5, 3, 5} => 17
                 0: 1  .  .  .  . .
                 1: . 10 15  5  . .
                 2: .  . 10 26 20 5
                    0  1  2  3  4 5
            {total: 1 10 26 32 20 5, 4, 1} => 2
                 0: 1  .  .  .  . .
                 1: . 10 15  6  . .
                 2: .  . 11 26 20 5

*-
bMs=unique apply(L7,data->data_0)
netList apply(bMs,b->(L7b=select(L7,data-> data_0==b);(b,tally sort apply(L7b,data->data_{1,2,4,3}))))
-*
      +-------------------------------------------------------------------+
      |        0  1  2  3  4 5                      0  1  2  3 4          |
o96 = |(total: 1 10 22 28 20 5, Tally{{2, 5, total: 1 11 20 11 1} => 244})|
      |     0: 1  .  .  .  . .                   0: 1  .  .  . .          |
      |     1: . 10 15  2  . .                   1: .  1  .  . .          |
      |     2: .  .  7 26 20 5                   2: . 10 20 11 .          |
      |                                          3: .  .  .  . 1          |
      |                                             0  1  2  3 4          |
      |                               {2, 6, total: 1 10 21 17 5} => 72   |
      |                                          0: 1  .  .  . .          |
      |                                          1: .  .  .  . .          |
      |                                          2: . 10 11  4 1          |
      |                                          3: .  . 10 13 4          |
      |                                             0  1  2  3 4          |
      |                               {2, 6, total: 1 11 17 10 3} => 52   |
      |                                          0: 1  .  .  . .          |
      |                                          1: .  .  .  . .          |
      |                                          2: . 11 15  2 .          |
      |                                          3: .  .  2  8 3          |
      |                                             0  1  2  3 4          |
      |                               {2, 6, total: 1 11 18 11 3} => 14   |
      |                                          0: 1  .  .  . .          |
      |                                          1: .  .  .  . .          |
      |                                          2: . 11 15  3 .          |
      |                                          3: .  .  3  8 3          |
      |                                             0  1  2  3 4          |
      |                               {2, 6, total: 1 11 22 17 5} => 11   |
      |                                          0: 1  .  .  . .          |
      |                                          1: .  .  .  . .          |
      |                                          2: . 10 12  4 1          |
      |                                          3: .  1 10 13 4          |
      |                                             0  1  2  3 4          |
      |                               {2, 6, total: 1 12 19 11 3} => 7    |
      |                                          0: 1  .  .  . .          |
      |                                          1: .  .  .  . .          |
      |                                          2: . 11 16  3 .          |
      |                                          3: .  1  3  8 3          |
      |                                             0  1  2  3 4          |
      |                               {2, 6, total: 1 12 23 17 5} => 5    |
      |                                          0: 1  .  .  . .          |
      |                                          1: .  .  .  . .          |
      |                                          2: . 10 13  4 1          |
      |                                          3: .  2 10 13 4          |
      |                                             0  1  2  3 4          |
      |                               {2, 6, total: 1 13 25 18 5} => 1    |
      |                                          0: 1  .  .  . .          |
      |                                          1: .  .  .  . .          |
      |                                          2: . 10 14  5 1          |
      |                                          3: .  3 11 13 4          |
      |                                             0  1  2  3 4          |
      |                               {2, 7, total: 1 10 24 21 6} => 11   |
      |                                          0: 1  .  .  . .          |
      |                                          1: .  .  .  . .          |
      |                                          2: .  7  3  . .          |
      |                                          3: .  3 21 21 6          |
      |                                             0  1  2  3 4          |
      |                               {3, 1, total: 1 10 16 10 3} => 36   |
      |                                          0: 1  .  .  . .          |
      |                                          1: .  .  .  . .          |
      |                                          2: .  9 11  1 .          |
      |                                          3: .  1  5  9 3          |
      |                                             0  1  2  3 4          |
      |                               {3, 1, total: 1 10 17 11 3} => 10   |
      |                                          0: 1  .  .  . .          |
      |                                          1: .  .  .  . .          |
      |                                          2: .  9 11  2 .          |
      |                                          3: .  1  6  9 3          |
      |                                             0  1  2  3 4          |
      |                               {3, 1, total: 1 11 19 12 3} => 6    |
      |                                          0: 1  .  .  . .          |
      |                                          1: .  .  .  . .          |
      |                                          2: .  9 12  3 .          |
      |                                          3: .  2  7  9 3          |
      |                                             0  1  2  3 4          |
      |                               {3, 1, total: 1 12 22 14 3} => 1    |
      |                                          0: 1  .  .  . .          |
      |                                          1: .  .  .  . .          |
      |                                          2: .  9 13  5 .          |
      |                                          3: .  3  9  9 3          |
      |                                             0  1  2 3 4           |
      |                               {2, 6, total: 1 11 15 8 3} => 64    |
      |                                          0: 1  .  . . .           |
      |                                          1: .  .  . . .           |
      |                                          2: . 11 15 . .           |
      |                                          3: .  .  . 8 3           |
      |                                             0  1  2 3 4           |
      |                               {2, 6, total: 1 11 16 9 3} => 79    |
      |                                          0: 1  .  . . .           |
      |                                          1: .  .  . . .           |
      |                                          2: . 11 15 1 .           |
      |                                          3: .  .  1 8 3           |
      |                                             0 1  2  3 4           |
      |                               {2, 6, total: 1 6 17 17 5} => 16    |
      |                                          0: 1 .  .  . .           |
      |                                          1: . 1  .  . .           |
      |                                          2: . 5  1  . .           |
      |                                          3: . . 16 17 5           |
      |                                             0 1  2  3 4           |
      |                               {2, 6, total: 1 7 18 17 5} => 5     |
      |                                          0: 1 .  .  . .           |
      |                                          1: . 1  .  . .           |
      |                                          2: . 5  2  . .           |
      |                                          3: . 1 16 17 5           |
      |                                             0 1  2  3 4           |
      |                               {2, 6, total: 1 8 19 17 5} => 7     |
      |                                          0: 1 .  .  . .           |
      |                                          1: . 1  .  . .           |
      |                                          2: . 5  3  . .           |
      |                                          3: . 2 16 17 5           |
      |                                             0 1  2  3 4           |
      |                               {2, 7, total: 1 9 23 21 6} => 220   |
      |                                          0: 1 .  .  . .           |
      |                                          1: . .  .  . .           |
      |                                          2: . 7  2  . .           |
      |                                          3: . 2 21 21 6           |
      |                                             0 1  2  3 4           |
      |                               {3, 1, total: 1 9 15 10 3} => 10    |
      |                                          0: 1 .  .  . .           |
      |                                          1: . .  .  . .           |
      |                                          2: . 9 10  1 .           |
      |                                          3: . .  5  9 3           |
      |                                             0 1  2 3 4            |
      |                               {3, 1, total: 1 9 14 9 3} => 155    |
      |                                          0: 1 .  . . .            |
      |                                          1: . .  . . .            |
      |                                          2: . 9 10 . .            |
      |                                          3: . .  4 9 3            |
      |                                             0 1  2 3 4            |
      |                               {3, 2, total: 1 8 14 9 2} => 176    |
      |                                          0: 1 .  . . .            |
      |                                          1: . 1  . . .            |
      |                                          2: . 7 14 9 2            |
      |                                             0 1 2                 |
      |                               {3, 3, total: 1 3 2} => 1           |
      |                                          0: 1 . .                 |
      |                                          1: . 3 2                 |
      |                                             0 1 2 3               |
      |                               {3, 2, total: 1 4 4 1} => 179       |
      |                                          0: 1 . . .               |
      |                                          1: . 3 2 .               |
      |                                          2: . 1 2 1               |
      |                                             0 1 2 3               |
      |                               {3, 2, total: 1 4 4 1} => 467       |
      |                                          0: 1 . . .               |
      |                                          1: . 4 4 1               |
      +-------------------------------------------------------------------+
      |        0  1  2  3  4 5                      0  1  2  3 4          |
      |(total: 1 10 23 29 20 5, Tally{{2, 7, total: 1 12 23 15 3} => 11}) |
      |     0: 1  .  .  .  . .                   0: 1  .  .  . .          |
      |     1: . 10 15  3  . .                   1: .  .  .  . .          |
      |     2: .  .  8 26 20 5                   2: .  8  9  3 .          |
      |                                          3: .  4 14 11 2          |
      |                                          4: .  .  .  1 1          |
      |                                             0  1  2  3 4          |
      |                               {2, 8, total: 1 13 25 15 2} => 54   |
      |                                          0: 1  .  .  . .          |
      |                                          1: .  .  .  . .          |
      |                                          2: .  5  3  . .          |
      |                                          3: .  8 22 14 .          |
      |                                          4: .  .  .  1 2          |
      |                                             0  1  2  3 4          |
      |                               {3, 1, total: 1 11 26 22 6} => 15   |
      |                                          0: 1  .  .  . .          |
      |                                          1: .  .  .  . .          |
      |                                          2: .  5  1  . .          |
      |                                          3: .  6 25 22 6          |
      |                                             0  1  2  3 4          |
      |                               {3, 1, total: 1 12 27 22 6} => 12   |
      |                                          0: 1  .  .  . .          |
      |                                          1: .  .  .  . .          |
      |                                          2: .  5  2  . .          |
      |                                          3: .  7 25 22 6          |
      |                                             0  1  2  3 4          |
      |                               {3, 1, total: 1 13 28 22 6} => 4    |
      |                                          0: 1  .  .  . .          |
      |                                          1: .  .  .  . .          |
      |                                          2: .  5  3  . .          |
      |                                          3: .  8 25 22 6          |
      |                                             0  1  2  3 4          |
      |                               {3, 2, total: 1 10 17 10 2} => 2    |
      |                                          0: 1  .  .  . .          |
      |                                          1: .  .  .  . .          |
      |                                          2: .  8 11  4 .          |
      |                                          3: .  1  3  3 1          |
      |                                          4: .  1  3  3 1          |
      |                                             0  1  2  3 4          |
      |                               {3, 2, total: 1 10 17 10 2} => 92   |
      |                                          0: 1  .  .  . .          |
      |                                          1: .  .  .  . .          |
      |                                          2: .  8 11  4 .          |
      |                                          3: .  2  6  6 2          |
      |                                             0  1  2  3 4          |
      |                               {3, 2, total: 1 10 19 13 3} => 43   |
      |                                          0: 1  .  .  . .          |
      |                                          1: .  .  .  . .          |
      |                                          2: .  7  8  3 .          |
      |                                          3: .  3 11 10 3          |
      |                                             0  1  2  3 4          |
      |                               {3, 2, total: 1 11 20 13 3} => 6    |
      |                                          0: 1  .  .  . .          |
      |                                          1: .  .  .  . .          |
      |                                          2: .  7  9  3 .          |
      |                                          3: .  4 11 10 3          |
      |                                             0 1  2 3 4            |
      |                               {3, 3, total: 1 9 15 9 2} => 1      |
      |                                          0: 1 .  . . .            |
      |                                          1: . .  . . .            |
      |                                          2: . 9 15 9 2            |
      |                                             0 1 2 3               |
      |                               {3, 3, total: 1 4 4 1} => 24        |
      |                                          0: 1 . . .               |
      |                                          1: . 2 1 .               |
      |                                          2: . 2 3 1               |
      |                                             0 1 2 3 4             |
      |                               {3, 2, total: 1 6 9 5 1} => 1       |
      |                                          0: 1 . . . .             |
      |                                          1: . 3 3 1 .             |
      |                                          2: . 3 6 4 1             |
      +-------------------------------------------------------------------+
      |        0  1  2  3  4 5                      0  1  2  3 4          |
      |(total: 1 10 24 30 20 5, Tally{{3, 2, total: 1 10 23 19 5} => 12}) |
      |     0: 1  .  .  .  . .                   0: 1  .  .  . .          |
      |     1: . 10 15  4  . .                   1: .  .  .  . .          |
      |     2: .  .  9 26 20 5                   2: .  4  .  . .          |
      |                                          3: .  6 23 19 5          |
      |                                             0  1  2  3 4          |
      |                               {3, 2, total: 1 11 21 13 2} => 2    |
      |                                          0: 1  .  .  . .          |
      |                                          1: .  .  .  . .          |
      |                                          2: .  4  2  . .          |
      |                                          3: .  7 19 13 1          |
      |                                          4: .  .  .  . 1          |
      |                                             0  1  2  3 4          |
      |                               {3, 2, total: 1 11 22 16 4} => 1    |
      |                                          0: 1  .  .  . .          |
      |                                          1: .  .  .  . .          |
      |                                          2: .  4  2  . .          |
      |                                          3: .  7 19 14 3          |
      |                                          4: .  .  1  2 1          |
      |                                             0  1  2  3 4          |
      |                               {3, 2, total: 1 12 23 16 4} => 1    |
      |                                          0: 1  .  .  . .          |
      |                                          1: .  .  .  . .          |
      |                                          2: .  5  5  1 .          |
      |                                          3: .  6 15 12 3          |
      |                                          4: .  1  3  3 1          |
      |                                             0  1  2  3 4          |
      |                               {3, 2, total: 1 13 24 15 3} => 1    |
      |                                          0: 1  .  .  . .          |
      |                                          1: .  .  .  . .          |
      |                                          2: .  4  4  1 .          |
      |                                          3: .  9 20 13 2          |
      |                                          4: .  .  .  1 1          |
      |                                             0  1  2  3 4          |
      |                               {3, 2, total: 1 13 25 17 4} => 1    |
      |                                          0: 1  .  .  . .          |
      |                                          1: .  .  .  . .          |
      |                                          2: .  4  4  1 .          |
      |                                          3: .  9 20 14 3          |
      |                                          4: .  .  1  2 1          |
      |                                             0  1  2  3 4          |
      |                               {3, 3, total: 1 10 18 12 3} => 6    |
      |                                          0: 1  .  .  . .          |
      |                                          1: .  .  .  . .          |
      |                                          2: .  5  5  1 .          |
      |                                          3: .  5 13 11 3          |
      |                                             0 1  2  3 4           |
      |                               {3, 3, total: 1 9 16 11 3} => 15    |
      |                                          0: 1 .  .  . .           |
      |                                          1: . .  .  . .           |
      |                                          2: . 5  4  . .           |
      |                                          3: . 4 12 11 3           |
      |                                             0 1  2 3 4            |
      |                               {3, 3, total: 1 8 13 8 2} => 1      |
      |                                          0: 1 .  . . .            |
      |                                          1: . .  . . .            |
      |                                          2: . 6  6 1 .            |
      |                                          3: . 2  7 7 2            |
      |                                             0 1 2 3               |
      |                               {3, 4, total: 1 4 4 1} => 8         |
      |                                          0: 1 . . .               |
      |                                          1: . 1 . .               |
      |                                          2: . 3 4 1               |
      +-------------------------------------------------------------------+
      |        0  1  2  3  4 5                      0 1  2  3 4           |
      |(total: 1 10 25 31 20 5, Tally{{3, 4, total: 1 9 17 12 3} => 5})   |
      |     0: 1  .  .  .  . .                   0: 1 .  .  . .           |
      |     1: . 10 15  5  . .                   1: . .  .  . .           |
      |     2: .  . 10 26 20 5                   2: . 3  1  . .           |
      |                                          3: . 6 16 12 3           |
      |                                             0 1  2 3 4            |
      |                               {3, 4, total: 1 8 14 9 2} => 1      |
      |                                          0: 1 .  . . .            |
      |                                          1: . .  . . .            |
      |                                          2: . 4  3 1 .            |
      |                                          3: . 4 11 8 2            |
      |                                             0 1 2                 |
      |                               {3, 5, total: 1 3 2} => 14          |
      |                                          0: 1 . .                 |
      |                                          1: . 1 .                 |
      |                                          2: . 2 2                 |
      |                                             0 1 2 3               |
      |                               {3, 5, total: 1 5 5 1} => 3         |
      |                                          0: 1 . . .               |
      |                                          1: . . . .               |
      |                                          2: . 5 5 1               |
      +-------------------------------------------------------------------+
      |        0  1  2  3  4 5                      0 1 2                 |
      |(total: 1 10 26 32 20 5, Tally{{4, 1, total: 1 2 1} => 2})         |
      |     0: 1  .  .  .  . .                   0: 1 . .                 |
      |     1: . 10 15  6  . .                   1: . 1 .                 |
      |     2: .  . 11 26 20 5                   2: . 1 1                 |
      +-------------------------------------------------------------------+

*-
netList apply(bMs,b->(L7b=select(L7,data-> data_0==b and data_4==0);(b,tally sort apply(L7b,data->data_{1,2,4,3}))))
-*
      +---------------------------------------------------------------------+
      |        0  1  2  3  4 5                         0  1  2  3 4         |
o99 = |(total: 1 10 22 28 20 5, Tally{{2, 5, 0, total: 1 11 20 11 1} => 18})|
      |     0: 1  .  .  .  . .                      0: 1  .  .  . .         |
      |     1: . 10 15  2  . .                      1: .  1  .  . .         |
      |     2: .  .  7 26 20 5                      2: . 10 20 11 .         |
      |                                             3: .  .  .  . 1         |
      |                                                0  1  2  3 4         |
      |                               {2, 6, 0, total: 1 11 17 10 3} => 2   |
      |                                             0: 1  .  .  . .         |
      |                                             1: .  .  .  . .         |
      |                                             2: . 11 15  2 .         |
      |                                             3: .  .  2  8 3         |
      |                                                0  1  2  3 4         |
      |                               {2, 6, 0, total: 1 11 18 11 3} => 1   |
      |                                             0: 1  .  .  . .         |
      |                                             1: .  .  .  . .         |
      |                                             2: . 11 15  3 .         |
      |                                             3: .  .  3  8 3         |
      |                                                0  1  2  3 4         |
      |                               {3, 1, 0, total: 1 10 16 10 3} => 1   |
      |                                             0: 1  .  .  . .         |
      |                                             1: .  .  .  . .         |
      |                                             2: .  9 11  1 .         |
      |                                             3: .  1  5  9 3         |
      |                                                0  1  2 3 4          |
      |                               {2, 6, 0, total: 1 11 15 8 3} => 18   |
      |                                             0: 1  .  . . .          |
      |                                             1: .  .  . . .          |
      |                                             2: . 11 15 . .          |
      |                                             3: .  .  . 8 3          |
      |                                                0  1  2 3 4          |
      |                               {2, 6, 0, total: 1 11 16 9 3} => 8    |
      |                                             0: 1  .  . . .          |
      |                                             1: .  .  . . .          |
      |                                             2: . 11 15 1 .          |
      |                                             3: .  .  1 8 3          |
      |                                                0 1  2  3 4          |
      |                               {2, 7, 0, total: 1 9 23 21 6} => 12   |
      |                                             0: 1 .  .  . .          |
      |                                             1: . .  .  . .          |
      |                                             2: . 7  2  . .          |
      |                                             3: . 2 21 21 6          |
      |                                                0 1  2 3 4           |
      |                               {3, 1, 0, total: 1 9 14 9 3} => 1     |
      |                                             0: 1 .  . . .           |
      |                                             1: . .  . . .           |
      |                                             2: . 9 10 . .           |
      |                                             3: . .  4 9 3           |
      +---------------------------------------------------------------------+
      |        0  1  2  3  4 5                         0  1  2  3 4         |
      |(total: 1 10 23 29 20 5, Tally{{3, 1, 0, total: 1 11 26 22 6} => 1}) |
      |     0: 1  .  .  .  . .                      0: 1  .  .  . .         |
      |     1: . 10 15  3  . .                      1: .  .  .  . .         |
      |     2: .  .  8 26 20 5                      2: .  5  1  . .         |
      |                                             3: .  6 25 22 6         |
      |                                                0  1  2  3 4         |
      |                               {3, 2, 0, total: 1 10 19 13 3} => 2   |
      |                                             0: 1  .  .  . .         |
      |                                             1: .  .  .  . .         |
      |                                             2: .  7  8  3 .         |
      |                                             3: .  3 11 10 3         |
      +---------------------------------------------------------------------+
      |        0  1  2  3  4 5                                              |
      |(total: 1 10 24 30 20 5, Tally{})                                    |
      |     0: 1  .  .  .  . .                                              |
      |     1: . 10 15  4  . .                                              |
      |     2: .  .  9 26 20 5                                              |
      +---------------------------------------------------------------------+
      |        0  1  2  3  4 5                                              |
      |(total: 1 10 25 31 20 5, Tally{})                                    |
      |     0: 1  .  .  .  . .                                              |
      |     1: . 10 15  5  . .                                              |
      |     2: .  . 10 26 20 5                                              |
      +---------------------------------------------------------------------+
      |        0  1  2  3  4 5                                              |
      |(total: 1 10 26 32 20 5, Tally{})                                    |
      |     0: 1  .  .  .  . .                                              |
      |     1: . 10 15  6  . .                                              |
      |     2: .  . 11 26 20 5                                              |
      +---------------------------------------------------------------------+
*-
/// -- end experimental values


	


moduleFromSchreyerSurface=method()
moduleFromSchreyerSurface(Ideal) := X -> (
    betti(fX:=res X);
    betti (fN:=res(coker transpose fX.dd_4));
    ideal fN.dd_5)

schreyerSurfaceFromModule=method()
schreyerSurfaceFromModule(Ideal) := M -> (
    fM:=res(M);
    kk:=coefficientRing ring M;
    rows:=positions(degrees fM_3,d->d=={4});
    columns:=positions(degrees fM_2,d->d=={3});
    N:=(fM.dd_3)^columns_rows;
    while(
	while(
	    while(n1:=random(kk^(rank source N),kk^2);
		N2:=map(P4^{15:-3},,N*n1);
	    not (dim coker transpose N2==0)) do();
	    m10x10:=(fM.dd_2_{0..14}*syz transpose syz(transpose N2,DegreeLimit=>-3));
	    betti(sm10x10:=syz transpose m10x10);
	    betti(X:=trim ideal((transpose sm10x10)*fM.dd_2));
	not(degree X ==11 and dim X==3)) do ();
        singX:=X+minors(2,jacobian X);
    dim singX !=0) do();
    X)


findRandomSmoothSchreyerSurface=method(Options=>{Verbose=>true})
findRandomSmoothSchreyerSurface(Ring) := opt -> (P4 -> (
    J:=null;singX:=null;
	if opt.Verbose==true then (
    while (
     elapsedTime while (J=findRandomSchreyerSurface P4;
	 dim (J+ideal jacobian J)!=0) do ();
	elapsedTime singX=J+minors(2,jacobian J);<<endl;
	elapsedTime dim singX !=0) do ();) else (
    while (
	while (J=findRandomSchreyerSurface P4; dim (J+ideal jacobian J)!=0) do ();
	 singX=J+minors(2,jacobian J);
	 dim singX !=0) do ());
   J))

findRandomSmoothSchreyerSurface(Ring,Number) := opt -> (P4,s) -> (
    X:=null;singX:=null;
    count:=1;
    while (
	elapsedTime while (X=findRandomSchreyerSurface(P4,s);
	    dim (X+ideal jacobian X)!=0) do (count=count+1);
	<<count <<endl;
	singX=X+minors(2,jacobian X);
	 dim singX !=0) do ();
   X)


collectSchreyerSurfaces=method()

collectSchreyerSurfaces(List,List,Number) :=(adjTypes,Ms,N) -> (
    --collect N smooth surfaces
    -- or discover a new family
    P4:= ring first Ms;
    adjTypes1:=adjTypes;Ms1:=Ms;adjTypes2={};Ms2:={};
    count:=0;count1:=0;
    X:= null; numList:=null; adjList:=null; ptsList:=null;M:= null;
    while (
    elapsedTime X=findRandomSmoothSchreyerSurface(P4,Verbose=>false);
    <<minimalBetti X << endl;count1=count1+1;
    <<count1 <<endl;
    elapsedTime (numList,adjList,ptsList,J)=adjunctionProcess(X,4);
    <<numList <<endl;
    adjTypes2=append(adjTypes2,numList);
    Ms2=append(Ms2,M);
    if not member(numList,adjTypes1)
    then (
	adjTypes1=append(adjTypes1,numList);
	M=moduleFromSchreyerSurface(X);
	Ms1=append(Ms1,M);
	count=count+1;
	<<count <<endl;
	<<numList <<endl;
	<<minimalBetti J <<endl;
	);
    count<1 and count1<N) do ();
    <<tally adjTypes2 <<endl;
    if count==1 then (adjTypes1,Ms1) else (adjTypes2,Ms2)
    )


collectSchreyerSurfaces(List,List,Number,Number) :=(adjTypes,Ms,s,N) -> ( 
    --collect N smooth s>=3 surfaces
    -- or discover a new family
    P4:=ring first Ms;
    adjTypes1=adjTypes;
    adjTypes2:={};Ms2:={};
    Ms1:=Ms;
    count:=0;count1:=0;
    X:= null; numList:=null; adjList:=null; ptsList:=null;M:= null;
    while (
    elapsedTime X=findRandomSmoothSchreyerSurface(P4,s);
    <<minimalBetti X << endl;count1=count1+1;
    <<count1 <<endl;
    elapsedTime (numList,adjList,ptsList,J)=adjunctionProcess(X,4);
    <<numList <<endl;
    adjTypes2=append(adjTypes2,numList);
    Ms2=append(Ms2,M);
    if not member(numList,adjTypes1)
    then (
	adjTypes1=append(adjTypes1,numList);
	M=moduleFromSchreyerSurface(X);
	Ms1=append(Ms1,M);
	count=count+1;
	<<count <<endl;
	<<numList <<endl;
	<<minimalBetti J <<endl;
	);
    count<1 and count1<N) do ();
    if count==1 then (adjTypes1,Ms1) else (adjTypes2,Ms2)
    )

///
P4=(ZZ/3)[x_0..x_4]
(Ms,adjTypes)=exampleOfSchreyerSurfaces(P4);
netList apply(9,i->(minimalBetti Ms_i,adjTypes_i))

Xs=apply(Ms_{4..6},M->elapsedTime schreyerSurfaceFromModule M);
setRandomSeed("two examples")
elapsedTime (adjTypes1,Ms1)=collectSchreyerSurfaces(adjTypes_{4..8},Ms_{4..8},3,3);
tally adjTypes1
#Ms1
elapsedTime (adjTypes1,Ms1)=collectSchreyerSurfaces(adjTypes_{7..8},Ms_{7..8},4,2);
tally adjTypes1
///


adjointTypes=method()
adjointTypes(List):= Ms -> (
    X:= null;L1:=null;L2:=null;J:=null;
    apply(Ms,M-> (
	    elapsedTime X=schreyerSurfaceFromModule(M);
	    elapsedTime (numList,L1,L2,J)=adjunctionProcess(X,4);
	    numList)
	)
    )

-------------------------------------
-- extension to charcteristic zero --
-------------------------------------
tangentDimension=method()
tangentDimension(Ideal) := (M) -> (
    -- computes the dimension tangent space at the strata with
    -- the same syzygies as M of G(5,S_2(V)) at the point M
    P4:= ring M;
    kk:=coefficientRing P4;
    fM:=res M;
    s:=rank fM_3-26;
    mons:=flatten entries sub(basis(2,P4/ideal fM.dd_1),P4);
    def1:=flatten apply(10,i->apply(mons,m->matrix{apply(10,j->
		if j==i then m else 0_P4)}));
    t:= symbol t;
    T:=kk[t_0..t_49];
    m7x2:=sum(50, i-> (d=def1_i;
	betti (d2=d*fM.dd_2//fM.dd_1);
	betti (d3=d2*fM.dd_3//fM.dd_2);
	T_i*sub(d3^{15..19+s}_{0..s-1},T)));
    50-codim ideal leadTerm mingens trim ideal m7x2)

exampleOfSchreyerSurfaces=method()
exampleOfSchreyerSurfaces(Ring) := P4 -> (
    if char P4 !=3 then error "expected coordinate ring of P4 in caharcteristic 3";
    Ms:={ideal(-x_0*x_2+x_1*x_2+x_0*x_3+x_2*x_3-x_0*x_4+x_1*x_4+x_2*x_4-x_3*x_4,x_1*x
      _2-x_1*x_3+x_2*x_3-x_3^2+x_0*x_4-x_1*x_4+x_2*x_4-x_3*x_4,x_0*x_2-x_1*x_2+x_0
      *x_3-x_1*x_3-x_0*x_4-x_2*x_4+x_4^2,-x_1*x_2+x_2^2-x_0*x_3+x_1*x_3+x_2*x_3+x_
      1*x_4-x_2*x_4+x_3*x_4-x_4^2,-x_1^2+x_0*x_3+x_3^2-x_0*x_4+x_1*x_4-x_2*x_4+x_3
      *x_4,-x_0*x_1+x_1^2-x_0*x_3-x_1*x_3+x_3^2+x_3*x_4,x_1^2-x_1*x_2-x_0*x_3-x_1*
      x_3+x_2*x_3+x_3^2-x_3*x_4+x_4^2,x_0*x_1-x_0*x_3-x_2*x_3+x_3^2-x_0*x_4-x_1*x_
      4+x_3*x_4+x_4^2,x_0^2-x_0*x_1-x_0*x_3-x_2*x_3+x_3^2-x_0*x_4-x_1*x_4+x_2*x_4-
      x_3*x_4-x_4^2,-x_0*x_1+x_0*x_2-x_0*x_3-x_2*x_3-x_0*x_4+x_2*x_4-x_3*x_4+x_4^2
      ), 
      ideal(-x_2*x_3+x_3^2-x_2*x_4-x_3*x_4+x_4^2,x_0*x_2+x_1*x_2+x_2^2+x_0*x_3-x_
      1*x_3+x_3^2+x_0*x_4+x_1*x_4-x_2*x_4-x_4^2,x_0*x_2-x_1*x_2+x_2^2-x_2*x_3+x_3^
      2+x_0*x_4-x_1*x_4-x_3*x_4-x_4^2,x_2^2+x_0*x_3+x_1*x_3-x_3^2+x_0*x_4+x_1*x_4+
      x_2*x_4+x_3*x_4-x_4^2,-x_0*x_1-x_1^2-x_1*x_2+x_0*x_3+x_2*x_3+x_3^2+x_2*x_4+x
      _3*x_4,-x_0*x_1+x_1^2-x_1*x_2+x_0*x_3-x_1*x_3+x_2*x_3+x_3^2-x_0*x_4+x_2*x_4-
      x_4^2,-x_1*x_2-x_0*x_3+x_1*x_3-x_2*x_3+x_3^2+x_0*x_4-x_1*x_4+x_2*x_4+x_4^2,x
      _0^2+x_0*x_1+x_0*x_2-x_0*x_3-x_1*x_3-x_2*x_3-x_3^2-x_1*x_4+x_2*x_4-x_3*x_4-x
      _4^2,x_0^2-x_0*x_1+x_0*x_2-x_0*x_3+x_2*x_3+x_3^2+x_0*x_4,x_0*x_2+x_0*x_3-x_1
      *x_3+x_2*x_3-x_3^2+x_0*x_4+x_1*x_4-x_2*x_4+x_3*x_4+x_4^2),
      ideal(x_1*x_3+x_2*x_3-x_3^2-x_0*x_4+x_1*x_4,-x_0*x_2-x_1*x_2-x_2^2+x_0*x_
      3-x_1*x_3-x_2*x_3-x_0*x_4-x_1*x_4+x_2*x_4,x_1*x_2-x_2^2-x_0*x_3+x_2*x_3+x_0*
      x_4+x_2*x_4+x_4^2,-x_1*x_2-x_2^2-x_0*x_3-x_1*x_3+x_2*x_3-x_0*x_4-x_1*x_4-x_3
      *x_4,x_0*x_1+x_1^2+x_1*x_2+x_0*x_3+x_3^2-x_0*x_4+x_3*x_4,-x_1^2+x_1*x_2+x_0*
      x_3+x_1*x_3-x_3^2+x_1*x_4+x_2*x_4-x_3*x_4+x_4^2,x_1^2+x_1*x_2+x_2*x_3+x_3^2-
      x_0*x_4-x_3*x_4,-x_0^2-x_0*x_1-x_0*x_2+x_0*x_3-x_1*x_3-x_2*x_3-x_3^2+x_0*x_4
      -x_1*x_4+x_4^2,x_0*x_1-x_0*x_2-x_1*x_3-x_2*x_3-x_3^2-x_1*x_4+x_2*x_4+x_4^2,-
      x_0*x_1-x_0*x_2-x_0*x_3+x_1*x_3-x_2*x_3+x_3^2-x_1*x_4+x_4^2),
      ideal(-x_0*x_3+x_1*x_3-x_2*x_3+x_3^2-x_0*x_4+x_1*x_4-x_2*x_4,-x_0*x_2+x_1*x_
      2-x_0*x_3-x_1*x_3-x_2*x_3+x_3^2-x_0*x_4+x_2*x_4+x_3*x_4+x_4^2,x_1*x_2+x_1*x_
      3-x_2*x_3-x_3*x_4,x_0*x_2-x_1*x_2+x_2^2+x_0*x_3-x_1*x_3+x_2*x_3+x_3^2+x_0*x_
      4-x_1*x_4,x_0*x_1-x_1^2+x_0*x_3+x_1*x_3+x_3^2+x_0*x_4+x_1*x_4+x_2*x_4+x_3*x_
      4+x_4^2,-x_1^2+x_1*x_4+x_2*x_4-x_3*x_4-x_4^2,-x_0*x_1+x_1^2-x_1*x_2-x_0*x_3+
      x_2*x_3+x_3^2-x_1*x_4-x_2*x_4+x_3*x_4,-x_0^2+x_0*x_1-x_0*x_3-x_2*x_3+x_3^2+x
      _0*x_4+x_1*x_4-x_3*x_4-x_4^2,x_0*x_1+x_0*x_3-x_1*x_3-x_2*x_3-x_3^2+x_0*x_4+x
      _1*x_4+x_2*x_4+x_3*x_4+x_4^2,x_0^2-x_0*x_1+x_0*x_2-x_0*x_3+x_1*x_3-x_2*x_3-x
      _3^2+x_1*x_4+x_2*x_4-x_3*x_4-x_4^2),
      ideal(-x_1*x_2+x_2^2+x_0*x_3-x_1*x_3+x_2*x_3+x_2*x_4-x_3*x_4,-x_0*x_2-x_1*x_
      2-x_1*x_4+x_2*x_4-x_3*x_4+x_4^2,-x_0*x_1-x_1^2-x_1*x_2-x_2*x_3+x_3^2+x_0*x_4
      -x_2*x_4+x_3*x_4,-x_0*x_1-x_1^2-x_1*x_3+x_3^2-x_0*x_4+x_1*x_4,x_1^2-x_1*x_2-
      x_0*x_3-x_3^2-x_0*x_4-x_1*x_4+x_2*x_4+x_3*x_4,x_0*x_1+x_1^2-x_0*x_3-x_1*x_3+
      x_2*x_3-x_3^2+x_1*x_4+x_3*x_4+x_4^2,x_0^2+x_0*x_1+x_0*x_2-x_0*x_4-x_1*x_4+x_
      2*x_4-x_3*x_4,x_0^2+x_0*x_1+x_0*x_3-x_1*x_3-x_3^2-x_0*x_4-x_1*x_4-x_2*x_4-x_
      3*x_4,-x_0*x_1+x_0*x_2-x_0*x_3+x_1*x_3+x_1*x_4+x_2*x_4+x_3*x_4+x_4^2,-x_0^2-
      x_0*x_1+x_0*x_3-x_3^2-x_1*x_4+x_3*x_4-x_4^2),
      ideal(x_0*x_2-x_1*x_2+x_2^2-x_0*x_3+x_2*x_3-x_0*x_4+x_2*x_4-x_3*x_4,-x_0*x_2
      +x_1*x_2-x_2^2+x_1*x_3+x_3^2-x_0*x_4+x_1*x_4-x_2*x_4+x_3*x_4-x_4^2,x_0*x_2+x
      _1*x_2-x_2*x_3+x_0*x_4+x_1*x_4-x_2*x_4+x_4^2,-x_0*x_2-x_1*x_2-x_2^2+x_0*x_3+
      x_0*x_4+x_2*x_4-x_3*x_4+x_4^2,x_0*x_1-x_1^2+x_1*x_2+x_1*x_3-x_2*x_3+x_3^2+x_
      0*x_4-x_1*x_4+x_2*x_4+x_3*x_4+x_4^2,-x_0*x_1-x_1^2+x_0*x_3+x_1*x_3-x_3^2+x_0
      *x_4-x_1*x_4-x_2*x_4+x_4^2,x_0*x_1+x_1^2+x_1*x_2+x_0*x_3-x_2*x_3-x_1*x_4+x_2
      *x_4-x_3*x_4+x_4^2,-x_0^2+x_0*x_1-x_0*x_2+x_0*x_3+x_1*x_3+x_3^2+x_0*x_4+x_4^
      2,x_0^2+x_0*x_1+x_3^2-x_2*x_4+x_3*x_4,-x_0^2-x_0*x_1-x_0*x_2-x_0*x_3+x_1*x_3
      +x_3^2-x_0*x_4+x_1*x_4+x_2*x_4-x_3*x_4-x_4^2),
      ideal(-x_0*x_2+x_2^2+x_1*x_3+x_2*x_3+x_3^2-x_1*x_4+x_2*x_4,x_1*x_2+x_2^2+x_0
      *x_3-x_3^2-x_0*x_4-x_1*x_4-x_3*x_4,x_0*x_2-x_1*x_2+x_0*x_3+x_1*x_3-x_3^2+x_1
      *x_4+x_2*x_4+x_3*x_4-x_4^2,-x_0*x_2-x_1*x_2+x_2^2-x_0*x_3-x_2*x_3+x_0*x_4+x_
      4^2,-x_1^2-x_1*x_2-x_0*x_3-x_1*x_3-x_2*x_3+x_3^2+x_2*x_4,-x_0*x_1+x_1^2+x_0*
      x_3-x_1*x_3-x_2*x_3-x_3^2-x_1*x_4+x_2*x_4-x_4^2,x_0*x_1+x_1^2-x_1*x_2+x_1*x_
      3-x_2*x_3-x_3^2+x_3*x_4-x_4^2,x_0*x_1+x_0*x_2+x_1*x_3+x_2*x_3+x_3^2-x_1*x_4+
      x_2*x_4-x_3*x_4-x_4^2,x_0^2-x_0*x_1-x_0*x_3+x_2*x_3-x_3^2+x_0*x_4-x_1*x_4+x_
      3*x_4+x_4^2,-x_0^2-x_0*x_1+x_0*x_2+x_2*x_3-x_1*x_4-x_2*x_4+x_3*x_4),
      ideal(x_0*x_2+x_0*x_3-x_1*x_3+x_3^2+x_0*x_4-x_1*x_4-x_3*x_4,-x_0*x_2+x_1*x_2
      -x_2^2+x_1*x_3+x_0*x_4+x_1*x_4-x_2*x_4+x_3*x_4-x_4^2,-x_2^2-x_0*x_3+x_1*x_3-
      x_2*x_3-x_0*x_4+x_3*x_4+x_4^2,x_1*x_2-x_2^2+x_0*x_3-x_1*x_3-x_2*x_3+x_3^2+x_
      0*x_4-x_1*x_4+x_2*x_4-x_4^2,x_0*x_1-x_1^2+x_1*x_2-x_0*x_3-x_1*x_3-x_2*x_3-x_
      0*x_4-x_1*x_4+x_3*x_4+x_4^2,x_1*x_2-x_3^2+x_0*x_4-x_1*x_4,-x_1^2+x_1*x_2-x_0
      *x_3+x_1*x_3-x_2*x_3+x_3^2+x_0*x_4-x_1*x_4-x_2*x_4-x_4^2,-x_0^2+x_0*x_1-x_0*
      x_2+x_0*x_3+x_1*x_3+x_2*x_3-x_3^2-x_0*x_4+x_1*x_4+x_2*x_4-x_3*x_4,-x_0*x_2+x
      _0*x_3+x_2*x_3-x_3^2+x_0*x_4+x_1*x_4,x_0*x_1-x_0*x_2-x_0*x_3+x_2*x_3-x_3^2+x
      _1*x_4), ideal(x_1*x_3-x_2*x_3-x_3^2-x_0*x_4-x_3*x_4,x_0*x_2+x_1*x_2+x_2^2+x
      _0*x_3+x_1*x_3+x_2*x_3+x_0*x_4+x_1*x_4+x_3*x_4-x_4^2,-x_0*x_1+x_1^2-x_1*x_2-
      x_0*x_3+x_2*x_3-x_0*x_4-x_2*x_4-x_3*x_4,-x_0*x_1-x_0*x_3-x_2*x_3+x_0*x_4-x_1
      *x_4-x_2*x_4-x_3*x_4,-x_0*x_3-x_1*x_3+x_2*x_3-x_0*x_4-x_1*x_4+x_2*x_4-x_4^2
      ,-x_0*x_1-x_1^2-x_1*x_2-x_0*x_3-x_1*x_3+x_2*x_3+x_3^2-x_0*x_4-x_2*x_4+x_3*x_
      4+x_4^2,x_0^2-x_0*x_1+x_0*x_2+x_0*x_3+x_1*x_3+x_2*x_3-x_0*x_4-x_1*x_4+x_2*x_
      4+x_3*x_4+x_4^2,x_0^2+x_0*x_3+x_1*x_3+x_3^2+x_0*x_4+x_2*x_4+x_3*x_4-x_4^2,-x
      _0*x_3-x_1*x_3-x_3^2+x_4^2,x_0^2+x_0*x_1+x_0*x_2+x_0*x_3+x_2*x_3+x_0*x_4+x_2
      *x_4-x_4^2)};
    adjTypes:={
      {(4,11,10), 5, (9,19,11), 1, (10,20,11), 0, (10,20,11), 0, (10,20,11)},
      {(4,11,10), 4, (9,19,11), 1, (10,19,10), 0, (9,16,8), 0, (7,11,5)},
      {(4,11,10), 3, (9,19,11), 1, (10,18,9), 2, (8,12,5), 4, (4,4,1)},
      {(4,11,10), 3, (9,19,11), 2, (10,18,9), 0, (8,13,6), 3, (5,6,2)},
      {(4,11,10), 2, (9,19,11), 3, (10,17,8), 2, (7,10,4), 2, (3,3,1)},
      {(4,11,10), 2, (9,19,11), 3, (10,17,8), 1, (7,10,4), 8, (3,2,0)},
      {(4,11,10), 2, (9,19,11), 2, (10,17,8), 4, (7,9,3), 7, (2,1,0)}, {(4,11,10),
      1, (9,19,11), 4, (10,16,7), 4, (6,7,2)}, {(4,11,10), 0, (9,19,11), 6,
      (10,15,6), 5, (5,5,1)}};
    (Ms,adjTypes)
    )
/// --discovered examples
P4=(ZZ/3)[x_0..x_4]
(Ms,adjTypes)=exampleOfSchreyerSurfaces(P4);
netList apply(9,i->(minimalBetti Ms_i,adjTypes_i))

elapsedTime Xs=apply(Ms_{0},M->schreyerSurfaceFromModule M);
netList apply(Xs,X->minimalBetti X)
Ts=apply(Xs,X->T=tateResolutionOfSurface X);
tally apply(Ts,T-> betti T)
m5x5s=apply(Ts,T-> T.dd_5_{5..9});
m5x5sP4=apply(m5x5s,m->sub(m,vars P4));
netList apply(m5x5sP4,m->(Q5=ideal det m; singQ5= trim(Q5+ideal jacobian Q5);
     (dim singQ5, degree singQ5, minimalBetti singQ5, betti saturate singQ5)))
Q5s=apply(m5x5sP4,m->ideal det m);
fourFoldPoints=apply(Q5s,q->trim ideal jacobian ideal jacobian ideal jacobian q);
apply(fourFoldPoints,J->(dim J, degree J, betti J))
triplePoints=apply(Q5s,q->trim ideal jacobian ideal jacobian q);
apply(triplePoints,J->(dim J, degree J, betti saturate J))
singQ5s=apply(Q5s,q->singQ5=saturate(q+ideal jacobian q));
netList apply(singQ5s,s->(dim s,degree s))
elapsedTime assSingQ5s=apply(singQ5s,s->ass s); -- 235.133 seconds elapsed
netList apply(assSingQ5s,L->tally apply(L,c->(dim c,degree c)))

dim2PartSingQ5s=apply(assSingQ5s,L->intersect prepend( ideal 1_P4,select(L,c->dim c==2)));
netList apply(dim2PartSingQ5s,c->(dim c, degree c, minimalBetti c, genus c))
singQ5s=apply(m5x5sP4,m->(Q5=ideal det m; singQ5= trim(Q5+ideal jacobian Q5);
     saturate singQ5));
netList apply(singQ5s,J->tally apply(decompose J,c->
	(dim c, degree c, minimalBetti c)))
-*
     +----------------------------------------------------------------------------------------------------------+
     |        0  1  2  3  4 5                                                                                   |
o6 = |(total: 1 10 22 28 20 5, {(4, 11, 10), 5, (9, 19, 11), 1, (10, 20, 11), 0, (10, 20, 11), 0, (10, 20, 11)})|
     |     0: 1  .  .  .  . .                                                                                   |
     |     1: . 10 15  2  . .                                                                                   |
     |     2: .  .  7 26 20 5                                                                                   |
     +----------------------------------------------------------------------------------------------------------+
     |        0  1  2  3  4 5                                                                                   |
     |(total: 1 10 22 28 20 5, {(4, 11, 10), 4, (9, 19, 11), 1, (10, 19, 10), 0, (9, 16, 8), 0, (7, 11, 5)})    |
     |     0: 1  .  .  .  . .                                                                                   |
     |     1: . 10 15  2  . .                                                                                   |
     |     2: .  .  7 26 20 5                                                                                   |
     +----------------------------------------------------------------------------------------------------------+
     |        0  1  2  3  4 5                                                                                   |
     |(total: 1 10 22 28 20 5, {(4, 11, 10), 3, (9, 19, 11), 1, (10, 18, 9), 2, (8, 12, 5), 4, (4, 4, 1)})      |
     |     0: 1  .  .  .  . .                                                                                   |
     |     1: . 10 15  2  . .                                                                                   |
     |     2: .  .  7 26 20 5                                                                                   |
     +----------------------------------------------------------------------------------------------------------+
     |        0  1  2  3  4 5                                                                                   |
     |(total: 1 10 22 28 20 5, {(4, 11, 10), 3, (9, 19, 11), 2, (10, 18, 9), 0, (8, 13, 6), 3, (5, 6, 2)})      |
     |     0: 1  .  .  .  . .                                                                                   |
     |     1: . 10 15  2  . .                                                                                   |
     |     2: .  .  7 26 20 5                                                                                   |
     +----------------------------------------------------------------------------------------------------------+
     |        0  1  2  3  4 5                                                                                   |
     |(total: 1 10 23 29 20 5, {(4, 11, 10), 2, (9, 19, 11), 3, (10, 17, 8), 2, (7, 10, 4), 2, (3, 3, 1)})      |
     |     0: 1  .  .  .  . .                                                                                   |
     |     1: . 10 15  3  . .                                                                                   |
     |     2: .  .  8 26 20 5                                                                                   |
     +----------------------------------------------------------------------------------------------------------+
     |        0  1  2  3  4 5                                                                                   |
     |(total: 1 10 23 29 20 5, {(4, 11, 10), 2, (9, 19, 11), 3, (10, 17, 8), 1, (7, 10, 4), 8, (3, 2, 0)})      |
     |     0: 1  .  .  .  . .                                                                                   |
     |     1: . 10 15  3  . .                                                                                   |
     |     2: .  .  8 26 20 5                                                                                   |
     +----------------------------------------------------------------------------------------------------------+
     |        0  1  2  3  4 5                                                                                   |
     |(total: 1 10 23 29 20 5, {(4, 11, 10), 2, (9, 19, 11), 2, (10, 17, 8), 4, (7, 9, 3), 7, (2, 1, 0)})       |
     |     0: 1  .  .  .  . .                                                                                   |
     |     1: . 10 15  3  . .                                                                                   |
     |     2: .  .  8 26 20 5                                                                                   |
     +----------------------------------------------------------------------------------------------------------+
     |        0  1  2  3  4 5                                                                                   |
     |(total: 1 10 24 30 20 5, {(4, 11, 10), 1, (9, 19, 11), 4, (10, 16, 7), 4, (6, 7, 2)})                     |
     |     0: 1  .  .  .  . .                                                                                   |
     |     1: . 10 15  4  . .                                                                                   |
     |     2: .  .  9 26 20 5                                                                                   |
     +----------------------------------------------------------------------------------------------------------+
     |        0  1  2  3  4 5                                                                                   |
     |(total: 1 10 25 31 20 5, {(4, 11, 10), 0, (9, 19, 11), 6, (10, 15, 6), 5, (5, 5, 1)})                     |
     |     0: 1  .  .  .  . .                                                                                   |
     |     1: . 10 15  5  . .                                                                                   |
     |     2: .  . 10 26 20 5                                                                                   |
     +----------------------------------------------------------------------------------------------------------+
*-

elapsedTime tally apply(#Ms,i->(M=Ms_i;(minimalBetti M,tangentDimension M)))
-*
 -- 7.56313 seconds elapsed

                     0  1  2  3  4 5
o104 = Tally{(total: 1 10 22 28 20 5, 36) => 4}
                  0: 1  .  .  .  . .
                  1: . 10 15  2  . .
                  2: .  .  7 26 20 5
                     0  1  2  3  4 5
             (total: 1 10 23 29 20 5, 34) => 3
                  0: 1  .  .  .  . .
                  1: . 10 15  3  . .
                  2: .  .  8 26 20 5
                     0  1  2  3  4 5
             (total: 1 10 24 30 20 5, 32) => 1
                  0: 1  .  .  .  . .
                  1: . 10 15  4  . .
                  2: .  .  9 26 20 5
                     0  1  2  3  4 5
             (total: 1 10 25 31 20 5, 30) => 1
                  0: 1  .  .  .  . .
                  1: . 10 15  5  . .
                  2: .  . 10 26 20 5
*-
///
-----------------------------------------
-- functions to analyze X              --
-----------------------------------------
sixSecantLocus=method()
sixSecantLocus(Ideal) := X -> (
    i:=#select(flatten degrees source gens X,d->d<6);
    X5:=ideal (gens X)_{0..i-1};
    R:=X5:X;
    <<(dim R, degree R, minimalBetti R) <<endl;
    if dim R==2 then (
    assert(degree (X+R) == 6* degree R);
    elapsedTime (numList,L1,L2,J):=adjunctionProcess(X,1);
    <<"Le Barz 6-secant formula is " <<LeBarzN6(degree X,(genera X)_1,1)==numList_1+degree R <<endl;
    return primaryDecomposition R);
    if dim R==3 then (
	cR:=primaryDecomposition R;
	<<tally apply(cR,c->(dim c, degree c, minimalBetti c, degree(X+c))) <<endl;
        surfaces:=select(cR,c->dim c==3);
    <<"surfaces: "<<tally apply(surfaces,c->(dim c,degree c,degree (c+X),
	    tally apply(primaryDecomposition(c+X),d->(dim d,degree d,degree radical d,minimalBetti d))))<<endl;
    curves:=select(cR,c->dim c==2);
    embeddedCurves:=select(flatten apply(surfaces,S->apply(curves,C->{S,C})),SC->dim sum SC==2);
    radEmbeddedCurves:=apply(embeddedCurves,SC->radical SC_1);
    apply(radEmbeddedCurves,C->(degree(C+X),degree radical (C+X),degree C));
    reducedCurves:=apply(curves,c->radical c);
    <<"reducedCurves: " <<tally apply(reducedCurves,c->(degree c,degree(c+X)))<<endl;
    <<"curves: "<<tally apply(curves,c->(degree c,degree (c+X),minimalBetti c))<<endl;
    comp:=surfaces|curves;
    return comp);
    )

tateResolutionOfSurface=method()
tateResolutionOfSurface(Ideal) := X -> (
    if not (dim X==3 and codim X==2) then error "expected the ideal of a surface in P4";
    P4:= ring X;
    kk:=coefficientRing P4;
    e:=symbol e;
    E:=kk[e_0..e_4,SkewCommutative=>true];
    m:=syz gens truncate(6,X);
    m':=symExt(m,E);
    T1:=res(coker m',LengthLimit=>8);
    T:=(dual T1)[-7]**E^{-6})
///
X=Xs_0;
betti(T=tateResolutionOfSurface X)    
///    

getSpecialARSurf=method()
--conjecture: these surfaces should end up in a conic bundle.
--n=115, P4=ZZ/7[x_0..x_4], kk=coefficientRing P4
getSpecialARSurf(PolynomialRing,Number) := (P4,n) -> (
    if not member(n,toList(113..115)) then error " expect n in {113..115}";
    kk:=coefficientRing P4;
    (E,m2x3,bs,as,B,ExB,E2,b4x2,a2x3,E3)=prepareAboRanestadSurfaces(P4);
    E'=kk[(gens E)_{0..2}];
    m4x2:=null;c:=null;I:=null;sol:=null;
    test:=0; count:=0;bb:=null;
    randSol:=null;b4x2r:=null;test1:=null;test2:=null;X:=null;singX:=null;
    count2:=0;
    n1:=min(116-n,2);m2x2:=null;
    m2xk:=map(kk^2,kk^0,0);
    scan(n1,c-> (
	    while (m2x2=random(kk^2,kk^2); det m2x2==0) do ();
	    m2xk=m2xk|m2x2*m2x3*random(kk^3,kk^1)));
    m2xk=m2xk|random(E^2,E^{2-n1:-1});
     while (
     while (
	test=0;
 	while (
    	count1=1;
	    while (	
--		m4x2=map(E^4,,transpose(sub(random(E'^2,E'^{2:-1}),E)|random(E^2,E^{2:-1})));
                m4x2=map(E^4,,transpose(sub(random(E'^2,E'^{2:-1}),E)|m2xk));
                c=b4x2*sub(m2x3,ExB)+sub(m4x2,ExB)*a2x3;
		I=trim ideal sub(contract(E3,flatten c),B);
	    not numgens I== n) do (count1=count1+1;);
	    <<"count1="<<count1<<endl;
	    --<<numgens I<<endl;
	    sol=vars B%I;
	    randSol=sub(sol,random(kk^1,kk^140));
	    b4x2r=sub(b4x2,vars E|randSol);
	    betti(bb=map(E^4,,m4x2|b4x2r));
	    test1 = degrees source syz bb =={{3}, {3}, {3}, {4}, {4}, {4}, {4}, {4}};
	    sbb=syz transpose bb;
	    test2=degrees source sbb=={{2}, {2}, {2}, {2}, {2}, {2}, {2}, {2}, {2}, {2}, {2}, {2}, {2}};
	    betti (Ts=res(coker sbb,LengthLimit=>3));
	    test3= (rank Ts_3==73); 
	    not(test1 and test2 and test3)) do (test=test+1;);
	<<"test="<<test<<endl;
        betti(T=res(coker bb, LengthLimit=>4));
	X=saturate ideal syz symExt(T.dd_4,P4);
	not(dim X==3 and degree X==12)) do (count2=count2+1;);
	<<"count2="<<count2<<endl;
	singX=X+minors(2,jacobian X);
	not dim singX == 0) do ();
        <<"non smooth examples="<<count2<<endl;
	X)

///
restart
needsPackage"BGG"
loadPackage "AdjunctionForSurfaces"
--viewHelp AdjunctionForSurfaces    
load"smoothRationalSurfacesInP4.m2"

P4=ZZ/nextPrime 10^3[x_0..x_4]
elapsedTime minimalBetti (X=getSpecialARSurf(P4,114))
elapsedTime (numList,L1,L2,J)=adjunctionProcess(X,4);
numList -- {(4, 12, 13), 7, (12, 24, 13), 4, (12, 19, 8), 5, (7, 8, 2)}
minimalBetti J, degree J
-*
              0  1  2  3 4 5
o174 = total: 1 13 30 25 9 2
           0: 1  .  .  . . .
           1: . 13 30 25 4 .
           2: .  .  .  . 5 2
*-
X5=ideal (gens X)_{0..4};
R=X5:X;minimalBetti R, degree R
tally apply(decompose R,c->(dim c, degree c, degree (c+X),minimalBetti c))
-*
                               0 1 2 3
o178 = Tally{(2, 2, 11, total: 1 3 3 1) => 1}
                            0: 1 2 1 .
                            1: . 1 2 1
                              0 1 2 3
             (2, 1, 6, total: 1 3 3 1) => 1
                           0: 1 3 3 1
*-
elapsedTime minimalBetti (X=getSpecialARSurf(P4,115))  -- 4.66018 seconds elapsed
elapsedTime (numList,L1,L2,J)=adjunctionProcess(X,4); -- 116.543 seconds elapsed
numList -- {(4, 12, 13), 6, (12, 24, 13), 7, (12, 18, 7), 2, (6, 7, 2)}
minimalBetti J, degree J
-*
               0 1  2 3 4
o184 = (total: 1 8 12 7 2, 7)
            0: 1 .  . . .
            1: . 8 12 3 .
            2: . .  . 4 2
*-
X5=ideal (gens X)_{0..4};
R=X5:X;minimalBetti R, degree R
tally apply(decompose R,c->(dim c, degree c, degree (c+X),minimalBetti c))
-*
                              0 1 2 3
o24 = Tally{(2, 2, 11, total: 1 3 3 1) => 1  }
                           0: 1 2 1 .
                           1: . 1 2 1
                              0 1 2 3 4
            (2, 2, 12, total: 1 5 8 5 1) => 1
                           0: 1 1 . . .
                           1: . 4 8 5 1
*-

P4=ZZ/nextPrime 101[x_0..x_4]
setRandomSeed("fast example")
elapsedTime minimalBetti (X=getSpecialARSurf(P4,113))   -- 8.20053 seconds elapsed
elapsedTime (numList,L1,L2,J)=adjunctionProcess(X,4); 
numList --  {(4, 12, 13), 8, (12, 24, 13), 1, (12, 20, 9), 8, (8, 9, 2)}
minimalBetti J, degree J
-*
              0  1  2  3  4  5 6
o29 = (total: 1 19 58 75 44 11 2, 9)
           0: 1  .  .  .  .  . .
           1: . 19 58 75 44  5 .
           2: .  .  .  .  .  6 2

*-
X5=ideal (gens X)_{0..4};
R=X5:X;minimalBetti R, degree R
tally apply(decompose R,c->(dim c, degree c, degree (c+X),minimalBetti c))
-*
                              0 1 2 3
o33 = Tally{(2, 2, 11, total: 1 3 3 1) => 1}
                           0: 1 2 1 .
                           1: . 1 2 1
*-
-- study the linked surfaces
P4=ZZ/nextPrime 10^3[x_0..x_4]
elapsedTime minimalBetti (X=getSpecialARSurf(P4,114))
ci=ideal (gens X*random(source gens X,P4^{2:-5}));
Y=ci:X;
minimalBetti Y
singY=Y + minors(2,jacobian Y);
dim singY==0
genera Y
betti(T=tateResolutionOfSurface Y)
betti(tateResolutionOfSurface X)
betti(omegaY=Ext^1(Y,P4^{-5}))
betti(presOmegaY=presentation omegaY)
betti(som=syz(presOmegaY^{3..6}))
betti(phi1=presOmegaY^{0..2}*som)
betti(fib=trim ideal(random(P4^1,P4^3)*phi1))
dim fib, degree fib
betti radical fib
-- Y -> P2 is generically 3:1 => Y is of general type
--elapsedTime (numList,L1,L2,J)=adjunctionProcess(Y,1);
X5=ideal (gens X)_{0..4};
R=X5:X;minimalBetti R, degree R
tally apply(cR=decompose R,c->(dim c, degree c, degree (c+X),minimalBetti c))
apply(cR,c->c+Y==c)
apply(cR,c->(c2=saturate(c^2+Y);(degree c,dim c2, degree c2, minimalBetti c2, degree c2,
	    genera c, genera c2, genus c2-genus c)))
--Oc2=L+Oc
--chiL=deg L +1, chiL=-(genus c2-genus c)==2 => deg L=-1
conic=first cR
line= last cR
betti(phiLine=trim coker (phi1%line))
kk=coefficientRing P4
P2=kk[z_0..z_2]
P2xP4=P2**P4
LP2=map(P2^4,,sub(contract(sub(basis(2,P4),P2xP4),transpose(sub(vars P2,P2xP4)*sub((presentation phiLine)_{0..3},P2xP4))),P2))
ann coker LP2
///
end




///
minimalBetti(X=Xs_1)
curves=sixSecantLocus(X);
tally apply(curves,C->(degree(C),degree(C+X)))
minimalBetti(X=Xs_0)
curves=sixSecantLocus(X);
tally apply(curves,C->(degree(C),degree(C+X)))
minimalBetti(X=Xs_2)
curves=sixSecantLocus(X);
tally apply(curves,C->(degree(C),degree(C+X)))
minimalBetti(X=Xs_3)
comp=sixSecantLocus(X);
tally apply(comp,C->(dim C,degree(C),degree(C+X)))
LeBarzN6(degree X,(genera X)_1,1)
minimalBetti(X=Xs_4)
comp=sixSecantLocus(X);
tally apply(comp,C->(dim C, degree(C),degree(C+X)))
minimalBetti(X=Xs_5)
comp=sixSecantLocus(X);
tally apply(comp,C->(dim C, degree(C),degree(C+X)))
minimalBetti(X=Xs_6)
comp=sixSecantLocus(X);
tally apply(comp,C->(dim C, degree(C),degree(C+X)))
minimalBetti(X=Xs_7)
comp=sixSecantLocus(X);
tally apply(comp,C->(dim C, degree(C),degree(C+X)))
minimalBetti(X=Xs_8)
comp=sixSecantLocus(X);
tally apply(comp,C->(dim C, degree(C),degree(C+X)))
///


    
    
    
restart
needsPackage"BGG"
loadPackage "AdjunctionForSurfaces"
--viewHelp AdjunctionForSurfaces    
load"smoothRationalSurfacesInP4.m2"

P4=(ZZ/3)[x_0..x_4]
(Ms,adjTypes)=exampleOfSchreyerSurfaces(P4);
netList apply(9,i->(minimalBetti Ms_i,adjTypes_i))
Xs=apply(Ms_{0},M->elapsedTime schreyerSurfaceFromModule M);
setRandomSeed("two examples")
elapsedTime (adjTypes1,Ms1)=collectSchreyerSurfaces(adjTypes,Ms,2); -- 98.783 seconds elapsed
#adjTypes1==#Ms1 -- if not true then we have a further new family
setRandomSeed("fast examplesA")
elapsedTime (adjTypes1,Ms1)=collectSchreyerSurfaces(adjTypes,Ms,3,1);
#adjTypes1==#Ms1 -- if not true then we have a further new family
end
-* construction section *-



elapsedTime minimalBetti (X=getSpecialARSurf(P4,115))


///
restart
needsPackage"BGG"
loadPackage "AdjunctionForSurfaces"
--viewHelp AdjunctionForSurfaces    
load"smoothRationalSurfacesInP4.m2"

kk=ZZ/nextPrime 10^3
P4=kk[x_0..x_4]
elapsedTime (Xs,adjTypes,m4x2s)=collectSmoothAboRanestadSurfaces(P4,116,1);
tally adjTypes
tally apply(Xs, X-> (X5=ideal (gens X)_{0..4};
	R=X5:X;
	tally apply(decompose R,c->(dim c, degree c, degree (c+X)))))
	
kk=ZZ/7
P4=kk[x_0..x_4]
N=116
elapsedTime minimalBetti(X=getSpecialARSurf(P4,116))
betti(fX=res(X,FastNonminimal=>true))
elapsedTime (numList,L1,L2,J)=adjunctionProcess(X,1);
///







randomSurface=method()
randomSurface(Function,Ring) := (F,P4) -> (
    X:=F(P4);
    (d,sg):=(degree X, sectionalGenus X);
    <<minimalBetti X << " cohomology "
    <<cohomologyTable(sheaf module X, -2,6) <<endl;
    <<"K2=" <<Ksquare(d,sg,1) <<", N6=" <<LeBarzN6(d,sg,1) <<endl;
    {d,sg})

randomSurface(Function,List) := (F,ringList) -> (
    (P4,E,P2):=(ringList_0,ringList_1,ringList_2);
    Larg:=toList first methods F;
    arguments :=drop(Larg,1);
    <<endl;
    <<Larg_0; <<endl;
    n:= #arguments; X:=null;
    elapsedTime (if n==1 then X=F(P4) ;
    if n==2 and member(Ring,arguments) then X=F(P4,E);
    if n==2 and not member(Ring,arguments) then X=F(P4,P2)); 
    (d,sg):=(degree X, sectionalGenus X);
    elapsedTime (<<minimalBetti X << " cohomology "
    <<cohomologyTable(sheaf module X, -2,6) <<endl);
    <<"K2=" <<Ksquare(d,sg,1) <<", N6=" <<LeBarzN6(d,sg,1) <<endl;
    {d,sg})

///
ringList={P4,E,P2}
F=degree10pi8RanestadSurface

randomSurface(F,P4)
Fs={cubicScroll,delPezzoSurface,castelnouvoSurface,bordigaSurface,ionescuOkonekSurface,
    degree8OkonekSurface,nonspecialAlexanderSurface,
    specialityOneAlexanderSurface,degree10pi8RanestadSurface,degree10pi9RanestadSurface,
    degree10DESSurface}

elapsedTime dgs=apply(Fs,F->randomSurface(F,ringList))
member(Ring,toList first methods degree8OkonekSurface)
S
F=degree8OkonekSurface
///
restart
needsPackage"BGG"
loadPackage "AdjunctionForSurfaces"
--viewHelp AdjunctionForSurfaces    
load"smoothRationalSurfacesInP4.m2"

kk=ZZ/nextPrime 10^3
P4=kk[x_0..x_4]
E=kk[e_0..e_4,SkewCommutative=>true]
P2=kk[t_0..t_2]

chiITable(11,11)
chiITable(13,15)    
TEST ///
minimalBetti(X=cubicScroll(P4)),degree X
genX=genera X
assert(chiITable(degree X,genX_1)=={0, 0, 0, 3, 13, 35, 75})

minimalBetti(X=veroneseSurface(P4,P2)),degree X
genX=genera X
assert(chiITable(degree X,genX_1)=={0, 0, -1, 0, 7, 25, 60})
///

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

elapsedTime  minimalBetti(X=degree8AlexanderSurface(P4,P2))
degree X, genera X
elapsedTime (numList,L1,l2,J)=adjunctionProcess(X,4);
numList, minimalBetti J
LeBarzN6(8,5,1)


elapsedTime  minimalBetti(X=degree8OkonekSurface(P4,E))
degree X , genera X

elapsedTime  minimalBetti(X=nonspecialAlexanderSurface(P4))
degree X, genera X
elapsedTime (numList,L1,l2,J)=adjunctionProcess(X,4);
numList, minimalBetti J


elapsedTime minimalBetti(X=nonspecialAlexanderSurface(P4,P2))

degree X, genera X

elapsedTime minimalBetti(X=specialityOneAlexanderSurface(P4,E))
degree X, genera X
elapsedTime (numList,L1,l2,J)=adjunctionProcess(X,4);
numList, minimalBetti J



elapsedTime minimalBetti(X=degree10pi8RanestadSurface(P4)) 
degree X, genera X
elapsedTime (numList,L1,l2,J)=adjunctionProcess(X,4); --
numList, minimalBetti J





elapsedTime minimalBetti(X=degree10pi9RanestadSurface(P4,E))
degree X, genera X
elapsedTime (numList,L1,l2,J)=adjunctionProcess(X,4);
numList, minimalBetti J


X5=ideal (gens X)_{0..6};
R=X5:X;
dim R, degree R, minimalBetti R
LeBarzN6(10,9,1)

elapsedTime minimalBetti(X=degree10DESSurface(P4,E))
degree X, genera X
degree X, genera X
elapsedTime (numList,L1,l2,J)=adjunctionProcess(X,4);
numList, minimalBetti J



minimalBetti(X=popescuSurface(P4,E,0))
singX=X+minors(2,jacobian X);
dim singX == 0
degree X, genera X
tex minimalBetti X
minimalBetti(X=popescuSurface(P4,E,1))
degree X,  genera X
X5=ideal (gens X)_{0..9};
R=X5:X;
dim R, degree R, minimalBetti R
singX=X+minors(2,jacobian X);
dim singX == 0
degree X, genera X
elapsedTime (numList,L1,l2,J)=adjunctionProcess(X,4);-- 11.7375 seconds elapsed
numList, minimalBetti J





minimalBetti(X=popescuSurface(P4,E,2))
degree X,  genera X
elapsedTime (numList,L1,l2,J)=adjunctionProcess(X,4);-- 11.7375 seconds elapsed
numList=={(4, 11, 11), 9, (10, 18, 9), 3, (8, 12, 5), 0, (4, 5, 2)}
minimalBetti J
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
X6=truncate(6,X);
minimalBetti X6
m=syz gens X6;
E=kk[e_0..e_4,SkewCommutative=>true]
M=symExt(m,E);
T=res (coker M,LengthLimit=>8)
betti ((dual T)[-7]**E^{-6})
tex betti ((dual T)[-7]**E^{-6})

kk=ZZ/2
P4=kk[x_0..x_4]
P2=kk[t_0..t_2]
E=kk[e_0..e_4,SkewCommutative=>true]
minimalBetti(X=bothmerSurface(P4,P2))
--elapsedTime (numList,L1,L2,J)=adjunctionProcess(X,4);
--numList, minimalBetti J


X6=truncate(6,X);
m=syz gens X6;
E=kk[e_0..e_4,SkewCommutative=>true]
M=symExt(m,E);
T1=res (coker M,LengthLimit=>8)
betti (T=((dual T1)[-7]**E^{-6}))
m2x2=T.dd_5^{1,2}_{10,11}
numgens trim ideal m2x2==4
m12x2=T.dd_5^{3,1,2}_{10,11}
betti (sm12x2t=syz transpose m12x2)
betti syz transpose sm12
tally apply(10,c->(betti (m21x3=map(target sm12x2t,,sm12x2t*random(source sm12x2t,E^{3:1})));
	betti (sm21x3=syz m21x3);
betti(m3x11=sm21x3*random(source sm21x3,E^{11:-1}));
betti res coker transpose m3x11))
betti res coker m121x3
----------------------------------------
-- Exploring Abo-Ranestad surfaces    --
----------------------------------------
kk=(ZZ/nextPrime 10^3)
P4=kk[x_0..x_4]
elapsedTime minimalBetti(X=first smoothAboRanestadSurface(P4,117))
--tex minimalBetti X
elapsedTime (numList,L1,L2,J)=adjunctionProcess(X,4);  -- 117.663 seconds elapsed
numList == {(4, 12, 13), 4, (12, 24, 13), 12, (12, 16, 5), 0, (4, 4, 1)}
minimalBetti J

X5=ideal (gens X)_{0..4};
d=degree X, sg=(genera X)_1
R=X5:X;
dim R, degree R, minimalBetti R, genus R
betti(singR=trim(R+minors(3,jacobian R)))
dim singR
LeBarzN6(d,sg,1)

kk=ZZ/nextPrime 10^3
P4=kk[x_0..x_4]
elapsedTime minimalBetti(X=first smoothAboRanestadSurface(P4,116))
elapsedTime (numList,L1,L2,J)=adjunctionProcess(X,4);
numList == {(4, 12, 13), 5, (12, 24, 13), 9, (12, 17, 6), 3, (5, 5, 1)}
Ksquare(12,13,1)==-12

X5=ideal (gens X)_{0..4};
d=degree X, sg=(genera X)_1
R=X5:X;
dim R, degree R
LeBarzN6(d,sg,1)

P4=ZZ/7[x_0..x_4]
elapsedTime minimalBetti(X=first smoothAboRanestadSurface(P4,115)) -- 29.666 seconds elapsed
elapsedTime (numList,L1,L2,J)=adjunctionProcess(X,4); -- 126.766 seconds elapsed
numList=={(4, 12, 13), 6, (12, 24, 13), 6, (12, 18, 7), 6, (6, 6, 1)}

X5=ideal (gens X)_{0..4};
d=degree X, sg=(genera X)_1
R=X5:X;
dim R, degree R
LeBarzN6(d,sg,1)

P4=ZZ/7[x_0..x_4]
elapsedTime minimalBetti(X=first smoothAboRanestadSurface(P4,114)) -- 54.388 seconds elapsed
elapsedTime (numList,L1,L2,J)=adjunctionProcess(X,4);-- 131.332 seconds elapsed
adjTypes={{(4, 12, 13), 7, (12, 24, 13), 4, (12, 19, 8), 5, (7, 8, 2)},{(4, 12, 13), 7, (12, 24, 13), 3, (12, 19, 8), 9, (7, 7, 1)}}
member(numList,adjTypes)

minimalBetti J
fJ=res J
betti(m2x5=fJ.dd_5^{4..8})
scroll=minors(2, m2x5);
degree scroll, dim scroll
minimalBetti scroll
trim ideal m2x5
-- scoll=S(2,1,1); J \cong 2H-2R,
dim scroll, dim J
degree scroll, degree J
degree J==2*5-2

X5=ideal (gens X)_{0..4};
d=degree X, sg=(genera X)_1
R=X5:X;
dim R, degree R
LeBarzN6(d,sg,1)
Ksquare(d,sg,1)

P4=ZZ/7[x_0..x_4]
elapsedTime minimalBetti(X=first smoothAboRanestadSurface(P4,113) -- 54.388 seconds elapsed
elapsedTime (numList,L1,L2,J)=adjunctionProcess(X,4);-- 131.332 seconds elapsed
adjTypes={{(4, 12, 13), 8, (12, 24, 13), 1, (12, 20, 9), 8, (8, 9, 2)}}
numList, minimalBetti J


setRandomSeed("112surface")
P4=(ZZ/7)[x_0..x_4]
--P4=(ZZ/nextPrime 500)[x_0..x_4]
	elapsedTime minimalBetti(X= first AboRanestadSurface(P4,113,4,10))
	
kk=coefficientRing P4
E=kk[e_0..e_4,SkewCommutative=>true]
elapsedTime betti(m29x68=syz gens truncate(6,X)) -- 65.0379 seconds elapsed
betti (T=res(coker symExt(m29x68,E)))
m3x2=T.dd_3^{5..7}_{0,1}
m2x4=T.dd_4^{2,3}
m3x2'=sub(m3x2,vars P4)
m2x4'=sub(m2x4,vars P4)
surf=minors(2,m3x2');
curve=minors(2,m2x4');
dim(curve+surf),dim curve, dim surf
degree(curve+surf)
pts=radical(curve+surf)
saturate(curve+surf)
degree pts, decompose pts
pt=first decompose pts
H=vars P4*syz contract(vars P4,transpose gens pt)
minimalBetti (XH=saturate(X+ideal H))
cohomologyTable(sheaf module XH,-5,5)
cohomologyTable(sheaf module X,-5,5)
minimalBetti (XH=saturate(X+ideal random(1,P4)))
cohomologyTable(sheaf module XH,-5,5)
H=vars P4*syz contract(vars P4, transpose (m2x4')^{0})
minimalBetti (XH=saturate(X+ideal H))
cohomologyTable(sheaf module XH,-5,5)
H=ideal(vars P4*syz contract(vars P4, (m3x2')_{1}))
minimalBetti (XH=saturate(X+ideal H_0))
cohomologyTable(sheaf module XH,-5,5)
setRandomSeed("newSurface")
P4=ZZ/7[x_0..x_4]
elapsedTime tally apply(1,c->(
	elapsedTime minimalBetti(X=smoothAboRanestadSurface(P4,112,4,10));  -- 69.173 seconds elapsed
	elapsedTime (numList,L1,L2,J)=adjunctionProcess(X,4);  -- 136.393 seconds elapse
	<< (betti X,numList,minimalBetti J) <<endl;
        numList))
betti X
numgens X
-*
(dim R, degree R)==(2, 3)
       0  1  2  3 4
total: 1 10 19 13 3
    0: 1  .  .  . .
    1: .  .  .  . .
    2: .  .  .  . .
    3: .  .  .  . .
    4: .  5  1  . .
    5: .  5 18 13 3
9882
20
 -- 354.722 seconds elapsed
*-
P4=ZZ/7[x_0..x_4]
elapsedTime minimalBetti(X=smoothAboRanestadSurface(P4,113,4))  -- 69.173 seconds elapsed
elapsedTime (numList,L1,L2,J)=adjunctionProcess(X,4);  -- 136.393 seconds elapsed
numList=={(4, 12, 13), 8, (12, 24, 13), 1, (12, 20, 9), 8, (8, 9, 2)}
minimalBetti J
fJ=res J
betti(m2x6=fJ.dd_6^{5..10})
scroll=minors(2, m2x6);
degree scroll, dim scroll
minimalBetti scroll
trim ideal m2x6
degree J
minimalBetti X
X5=ideal (gens X)_{0..4};
R=X5:X;
dim R, degree R, minimalBetti R
dim (R+X),degree (R+X)
singR=(R+minors(3,jacobian R));
dim singR
-- => R is a smooth plane conic, which intersects X in 11 points.
LeBarzN6(12,13,1)==8

elapsedTime tally apply(10,c-> (elapsedTime X=smoothAboRanestadSurface(P4,113,4);
    --if rank source gens X >9 then (<< toString X <<endl);
    minimalBetti X))
-* 
                   0  1  2  3 4
o85 = Tally{total: 1 10 19 13 3 => 4}
                0: 1  .  .  . .
                1: .  .  .  . .
                2: .  .  .  . .
                3: .  .  .  . .
                4: .  5  1  . .
                5: .  5 18 13 3
                   0 1  2  3 4
            total: 1 9 18 13 3 => 6
                0: 1 .  .  . .
                1: . .  .  . .
                2: . .  .  . .
                3: . .  .  . .
                4: . 5  .  . .
                5: . 4 18 13 3
*-
count=1
elapsedTime while (elapsedTime X=smoothAboRanestadSurface(P4,113,4);
    rank source gens X <10) do (count=count+1); count
minimalBetti X
fX=res X
betti trim ideal fX.dd_2_{0}
X4=ideal ((gens X)_{0..4}*diff( vars P4, (fX.dd_2^{0..4}_{0})))
degree X4
minimalBetti X4
degree X4
R4=X4:X;
dim R4, degree R4
R4=X4:X5
degree R4, dim R4, minimalBetti R4
minimalBetti saturate R4
elapsedTime (numList,L1,L2,J)=adjunctionProcess(X,4);  -- 136.393 seconds elapsed
numList =={(4, 12, 13), 4, (12, 24, 13), 12, (12, 16, 5), 0, (4, 4, 1)}

X5=ideal(gens X)_{0..4};
R=X5:X;
dim R, degree R, minimalBetti R
dim (R+X), degree(R+X)

--------------------------------
-- exploring Schreyer surface --
--------------------------------


kk=ZZ/3
P4=kk[x_0..x_4]
setRandomSeed("surface1") -- p=3 -- 14.6751 seconds elapsed
elapsedTime betti (X=findRandomSmoothSchreyerSurface P4) -- 32.6146 seconds elapsed
minimalBetti X
elapsedTime (numList,adjList,ptsList,J)=adjunctionProcess(X,5);-- 13.5415 seconds elapsed
numList=={(4, 11, 10), 4, (9, 19, 11), 1, (10, 19, 10), 0, (9, 16, 8), 0, (7, 11, 5), 5, (4, 4, 1)}
minimalBetti J

setRandomSeed("surface2a")
elapsedTime betti (X=findRandomSmoothSchreyerSurface(P4,Verbose=>false))  -- 133.547 seconds elapsed
elapsedTime (numList,adjList,ptsList,J)=adjunctionProcess(X,4); -- 14.9475 seconds elapsed
numList== {(4, 11, 10), 5, (9, 19, 11), 1, (10, 20, 11), 0, (10, 20, 11), 0, (10, 20, 11)}

setRandomSeed("surface3b")
elapsedTime betti (X=findRandomSmoothSchreyerSurface(P4,Verbose=>false))  --  -- 12.3789 seconds elapsed
elapsedTime (numList,adjList,ptsList,J)=adjunctionProcess(X,4); -- 15.7587 seconds elapsed
numList=={(4, 11, 10), 3, (9, 19, 11), 1, (10, 18, 9), 2, (8, 12, 5), 4, (4, 4, 1)}
minimalBetti J
Ksquare(11,10,1)

setRandomSeed("surface4a")
elapsedTime betti (X=findRandomSmoothSchreyerSurface(P4,Verbose=>false)) -- 175.104 seconds elapsed 
minimalBetti X
elapsedTime (numList,adjList,ptsList,J)=adjunctionProcess(X,4);  -- 13.0141 seconds elapsed
numList=={(4, 11, 10), 0, (9, 19, 11), 6, (10, 15, 6), 5, (5, 5, 1)}
minimalBetti J


elapsedTime tally apply(Ms_{0}, M -> (
	elapsedTime X=schreyerSurfaceFromModule M;
	<< minimalBetti X <<endl;
	elapsedTime (numList,adjList,ptsList,J)=adjunctionProcess(X,4); 
	<<numList <<endl;
	<<minimalBetti J <<endl;
	numList))
restart

restart
needsPackage"BGG"
loadPackage "AdjunctionForSurfaces"
--viewHelp AdjunctionForSurfaces    
load"smoothRationalSurfacesInP4.m2"
P4=(ZZ/3)[x_0..x_4]
(Ms,adjTypes)=exampleOfSchreyerSurfaces(P4);
netList apply(9,i->(minimalBetti Ms_i,adjTypes_i))

elapsedTime Xs=apply(Ms_{0,1,2,3},M->schreyerSurfaceFromModule M);
tally  apply(Xs,X->minimalBetti X)

X=Xs_1;
X5=ideal (gens X)_{0..4};
R=X5:X;
dim R, degree R
minimalBetti R
degree radical R
apply(decompose R,c->minimalBetti c)
apply(primaryDecomposition R,c->(minimalBetti c,minimalBetti radical c))
genus R
betti(fR=res R)
minimalBetti coker transpose  fR.dd_4
apply(10,i->hilbertFunction(i-10,coker transpose fR.dd_4))

minimalBetti (ideal fR.dd_4+ideal R_0)
R_0

binomial(4+2,2)

--Kristians construction
P4=ZZ/nextPrime 10^3[x_0..x_4]
planes=apply(5,i->ideal(x_i,x_((i+1)%5)))

minimalBetti(ps= intersect planes)
Ls=apply(planes,i->i+ideal random(1,P4))
betti(L=intersect Ls)
cub=ideal(gens L*random(source gens L,P4^{-3}))
C=(intersect planes+cub):L;
betti(fC=res C)
apply(primaryDecomposition (C+X),c->betti c)
M=ideal fC.dd_4^{1..10} 
minimalBetti M
X=schreyerSurfaceFromModule M;
minimalBetti X
X5=ideal (gens X)_{0..4};
R=X5:X;
dim R, degree R
dim(R+X), degree (R+X)
tally apply(decompose(R+X),c->(dim c, degree c, minimalBetti radical c))
tally apply(planes,c->(dim c, degree (c+C), tally apply(decompose(c+C),d->(degree d,dim d,minimalBetti d)))
)
tally apply(planes,c->(dim c, degree (c+X), tally apply(decompose(c+X),d->(degree d,dim d,minimalBetti d))))
saturate(X+sum planes_{0,1})
conics=decompose C
p1=saturate(sum conics_{0,1})
p2=saturate(sum conics_{1,5})
p3=intersect(decompose(ideal(x_0,x_4)+X))_{1,2,3}
degree trim(p3+conics_1)
degree intersect(p1,p2,p3)
minimalBetti R
intersect ass R
decompose R
primaryDecomposition R
singX =X +minors(2, jacobian X);
dim singX
elapsedTime (numList, L1,L2,J)=adjunctionProcess(X,3);
numList
minimalBetti J
