
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

degree8AlexanderSurface=method()
degree8AlexanderSurface(Ring,Ring) := (P4,P2) -> (
    H:= intersect (apply(10,i->(ideal random(P2^1,P2^{2:-1}))^2)|{ideal random(P2^1,P2^{2:-1})});
    X:= trim ker map(P2,P4,gens H);
    assert(dim X==3 and degree X==8 and (genera X)_1==5);
    X)


nonspecialAlexanderSurface=method()
nonspecialAlexanderSurface(Ring) := P4 -> (
    betti(L :=matrix{{P4_0,P4_1,P4_2}}|random(P4^1,P4^{15:-2}));
    betti(L2 :=map(P4^{3:-1},P4^{3:-1},0)|random(P4^{3:-1},P4^{15:-2}));
    betti (N:=transpose (transpose L| transpose L2));
    betti (fN:=res coker N);
    X:=trim ideal (fN.dd_4*syz fN.dd_4^{16..21});
    assert(dim X==3 and degree X==9 and (genera X)_1==6);
    X)


nonspecialAlexanderSurface(Ring,Ring) := (P4,P2) -> (
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

bothmerSurface=method()
bothmerSurface(Ring,Ring) := (P4,P2) -> (
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

---------------------------------------
--      Abo-Ranestad surfaces        --
---------------------------------------

prepareAboRanestadSurfaces=method()
prepareAboRanestadSurfaces(Ring) := P4 -> (
    kk:=coefficientRing P4;
    --assert(member(char(kk),{2,3,5,7,11,13}));
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
AboRanestadSurface(Ring,Number,Number) := (P4,n,k) -> (
    assert(member(n,toList(112..117)));
    kk:= coefficientRing P4;
    (E,m2x3,bs,as,B,ExB,E2,b4x2,a2x3,E3):=prepareAboRanestadSurfaces(P4);
    assert(n+k <121);
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
    X)

smoothAboRanestadSurface=method()
smoothAboRanestadSurface(Ring,Number,Number) := (P4,n,k) -> (
    assert(member(n,toList(112..117)));
    assert(n+k <121);
    countSmooth:=1;singX:=null;X:=null;
    while (
	elapsedTime X=AboRanestadSurface(P4,n,k);
	singX=X+minors(2,jacobian X);
	dim singX !=0 ) do (countSmooth=countSmooth+1);
    <<countSmooth;
    X)

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
     elapsedTime while (J=findRandomSchreyerSurface P4; dim (J+ideal jacobian J)!=0) do ();
	elapsedTime singX=J+minors(2,jacobian J);<<endl;
	elapsedTime dim singX !=0) do ();) else (
    while (
	while (J=findRandomSchreyerSurface P4; dim (J+ideal jacobian J)!=0) do ();
	 singX=J+minors(2,jacobian J);
	 dim singX !=0) do ());
   J))

findRandomSmoothSchreyerSurface(Ring,Number) := opt -> (P4,s) -> (
    X:=null;singX:=null;
    while (
	while (X=findRandomSchreyerSurface(P4,s); dim (X+ideal jacobian X)!=0) do ();
	 singX=X+minors(2,jacobian X);
	 dim singX !=0) do ();
   X)


collectSchreyerSurfaces=method()

	
collectSchreyerSurfaces(List,List,Ring,Number) :=(adjTypes,Ms,P4,N) -> ( 
    adjTypes1:=adjTypes;Ms1:=Ms;
    count:=0;count2:=0;
    X:= null; numList:=null; adjList:=null; ptsList:=null;M:= null;
    while (
    elapsedTime X=findRandomSmoothSchreyerSurface(P4,Verbose=>false);
    <<minimalBetti X << endl;count2=count2+1;
    <<count2 <<endl;
    elapsedTime (numList,adjList,ptsList,J)=adjunctionProcess(X,4);
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
    count<N) do ();
    (adjTypes1,Ms1)
    )

collectSchreyerSurfaces(List,Number,Ring,Number) :=(Ms,s,P4,N) -> ( 
    if s<3 then error "expected number of extra syzygies >2";
    elapsedTime (adjTypes1=adjointTypes(Ms));
    << tally adjTypes1 <<endl;
    Ms1:=Ms;
    count:=0;count1:=0;
    X:= null; numList:=null; adjList:=null; ptsList:=null;M:= null;
    while (
    elapsedTime X=findRandomSmoothSchreyerSurface(P4,s);
    <<minimalBetti X << endl;count1=count1+1;
    <<count1 <<endl;
    elapsedTime (numList,adjList,ptsList,J)=adjunctionProcess(X,4);
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
    count<N) do ();
    Ms1)

adjointTypes=method()
adjointTypes(List):= Ms -> (
    X:= null;L1:=null;L2:=null;J:=null;
    apply(Ms,M-> (
	    X=schreyerSurfaceFromModule(M);
	    elapsedTime (numList,L1,L2,J)=adjunctionProcess(X,4);
	    numList)
	)
    )


end

---%%%%%%%%%%%%%%%%%%%%
restart
needsPackage"BGG"
loadPackage "AdjunctionForSurfaces"
--viewHelp AdjunctionForSurfaces    
load"smoothRationalSurfacesInP4.m2"
--peek loadedFiles





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
tex minimalBetti X
LeBarzN6(8,5,1)

X5=ideal (gens X)_{0..4};
R=X5:X;
dim R,degree R
cR=primaryDecomposition R;
apply(cR,c->(dim c, degree c, minimalBetti c,dim(c+X),degree (c+X),minimalBetti (c+X), genera(c+X)))

elapsedTime  minimalBetti(X=degree8OkonekSurface(P4,E))
degree X , genera X

elapsedTime  minimalBetti(X=nonspecialAlexanderSurface(P4))
degree X, genera X

elapsedTime minimalBetti(X=nonspecialAlexanderSurface(P4,P2))

degree X, genera X

elapsedTime minimalBetti(X=specialityOneAlexanderSurface(P4,E))
degree X, genera X

elapsedTime minimalBetti(X=degree10pi8RanestadSurface(P4)) 
degree X

elapsedTime minimalBetti(X=degree10pi9RanestadSurface(P4,E))
degree X, genera X
tex minimalBetti X
X5=ideal (gens X)_{0..6};
R=X5:X;
dim R, degree R, minimalBetti R
LeBarzN6(10,9,1)

elapsedTime minimalBetti(X=degree10DESSurface(P4,E))
degree X, genera X
tex minimalBetti X



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


minimalBetti(X=popescuSurface(P4,E,2))
degree X,  genera X
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

----------------------------------------
-- Exploring Abo-Ranestad surfaces    --
----------------------------------------
elapsedTime minimalBetti(X=smoothAboRanestadSurface(P4,117,3))
--tex minimalBetti X
elapsedTime (numList,L1,L2,J)=adjunctionProcess(X,4);  -- 117.663 seconds elapsed
numList == {(4, 12, 13), 4, (12, 24, 13), 12, (12, 16, 5), 0, (4, 4, 1)}


X5=ideal (gens X)_{0..4};
d=degree X, sg=(genera X)_1
R=X5:X;
dim R, degree R, minimalBetti R, genus R
betti(singR=trim(R+minors(3,jacobian R)))
dim singR
LeBarzN6(d,sg,1)

elapsedTime minimalBetti(X=smoothAboRanestadSurface(P4,116,4))
elapsedTime (numList,L1,L2,J)=adjunctionProcess(X,4);
numList == {(4, 12, 13), 5, (12, 24, 13), 9, (12, 17, 6), 3, (5, 5, 1)}
Ksquare(12,13,1)==-12

X5=ideal (gens X)_{0..4};
d=degree X, sg=(genera X)_1
R=X5:X;
dim R, degree R
LeBarzN6(d,sg,1)

P4=ZZ/7[x_0..x_4]
elapsedTime minimalBetti(X=smoothAboRanestadSurface(P4,115,4)) -- 29.666 seconds elapsed
elapsedTime (numList,L1,L2,J)=adjunctionProcess(X,4); -- 126.766 seconds elapsed
numList=={(4, 12, 13), 6, (12, 24, 13), 6, (12, 18, 7), 6, (6, 6, 1)}

X5=ideal (gens X)_{0..4};
d=degree X, sg=(genera X)_1
R=X5:X;
dim R, degree R
LeBarzN6(d,sg,1)

P4=ZZ/7[x_0..x_4]
elapsedTime minimalBetti(X=smoothAboRanestadSurface(P4,114,4)) -- 54.388 seconds elapsed
elapsedTime (numList,L1,L2,J)=adjunctionProcess(X,4);-- 131.332 seconds elapsed
numList ==  {(4, 12, 13), 7, (12, 24, 13), 4, (12, 19, 8), 5, (7, 8, 2)}
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
elapsedTime tally apply(3,c->(
	elapsedTime minimalBetti(X=smoothAboRanestadSurface(P4,112,4));  -- 69.173 seconds elapsed
	elapsedTime (numList,L1,L2,J)=adjunctionProcess(X,4);  -- 136.393 seconds elapse
	<< (betti X,numList,minimalBetti J) <<endl;
        numList))

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
elapsedTime (numList,adjList,ptsList,J)=adjunctionProcess(X,4);  -- 13.0141 seconds elapsed
numList=={(4, 11, 10), 0, (9, 19, 11), 6, (10, 15, 6), 5, (5, 5, 1)}
minimalBetti J


elapsedTime tally apply(Ms_{4}, M -> (
	elapsedTime X=schreyerSurfaceFromModule M;
	<< minimalBetti X <<endl;
	elapsedTime (numList,adjList,ptsList,J)=adjunctionProcess(X,4); 
	<<numList <<endl;
	<<minimalBetti J <<endl;
	numList))
-- with input data from the d=11pi=10 file

--adjTypes={};Ms={}; P4=(ZZ/3)[x_0..x_4]
string="surface1aa";N=2;
elapsedTime (adjTypes,Ms)=collectSchreyerSurfaces(adjTypes,Ms,P4,1);
#Ms
Ms=Ms1
tally adjTypes
tally apply(Ms,M->minimalBetti M)
adjTypes=adjointTypes Ms
tally adjTypes2
toString Ms
-*
-- Example Data for s=2 surfaces --
P4=(ZZ/3)[x_0..x_4]
Ms={ideal(-x_2*x_3+x_3^2-x_2*x_4-x_3*x_4+x_4^2,x_0*x_2+x_1*x_2+x_2^2+x_0*x_3-x_1*x_3+x_3^2+x_0*x_4+x_1*x
      _4-x_2*x_4-x_4^2,x_0*x_2-x_1*x_2+x_2^2-x_2*x_3+x_3^2+x_0*x_4-x_1*x_4-x_3*x_4-x_4^2,x_2^2+x_0*x_3+x_1*
      x_3-x_3^2+x_0*x_4+x_1*x_4+x_2*x_4+x_3*x_4-x_4^2,-x_0*x_1-x_1^2-x_1*x_2+x_0*x_3+x_2*x_3+x_3^2+x_2*x_4+
      x_3*x_4,-x_0*x_1+x_1^2-x_1*x_2+x_0*x_3-x_1*x_3+x_2*x_3+x_3^2-x_0*x_4+x_2*x_4-x_4^2,-x_1*x_2-x_0*x_3+x
      _1*x_3-x_2*x_3+x_3^2+x_0*x_4-x_1*x_4+x_2*x_4+x_4^2,x_0^2+x_0*x_1+x_0*x_2-x_0*x_3-x_1*x_3-x_2*x_3-x_3^
      2-x_1*x_4+x_2*x_4-x_3*x_4-x_4^2,x_0^2-x_0*x_1+x_0*x_2-x_0*x_3+x_2*x_3+x_3^2+x_0*x_4,x_0*x_2+x_0*x_3-x
      _1*x_3+x_2*x_3-x_3^2+x_0*x_4+x_1*x_4-x_2*x_4+x_3*x_4+x_4^2),
      ideal(-x_0*x_2+x_1*x_2+x_0*x_3+x_2*x_3-x_0*x_4+x_1*x_4+x_2*x_4-x_3*x_4,x_1*x_2-x_1*x_3+x_2*x_3-x_3^2+
      x_0*x_4-x_1*x_4+x_2*x_4-x_3*x_4,x_0*x_2-x_1*x_2+x_0*x_3-x_1*x_3-x_0*x_4-x_2*x_4+x_4^2,-x_1*x_2+x_2^2-
      x_0*x_3+x_1*x_3+x_2*x_3+x_1*x_4-x_2*x_4+x_3*x_4-x_4^2,-x_1^2+x_0*x_3+x_3^2-x_0*x_4+x_1*x_4-x_2*x_4+x_
      3*x_4,-x_0*x_1+x_1^2-x_0*x_3-x_1*x_3+x_3^2+x_3*x_4,x_1^2-x_1*x_2-x_0*x_3-x_1*x_3+x_2*x_3+x_3^2-x_3*x_
      4+x_4^2,x_0*x_1-x_0*x_3-x_2*x_3+x_3^2-x_0*x_4-x_1*x_4+x_3*x_4+x_4^2,x_0^2-x_0*x_1-x_0*x_3-x_2*x_3+x_3
      ^2-x_0*x_4-x_1*x_4+x_2*x_4-x_3*x_4-x_4^2,-x_0*x_1+x_0*x_2-x_0*x_3-x_2*x_3-x_0*x_4+x_2*x_4-x_3*x_4+x_4
      ^2), ideal(x_1*x_3+x_2*x_3-x_3^2-x_0*x_4+x_1*x_4,-x_0*x_2-x_1*x_2-x_2^2+x_0*x_3-x_1*x_3-x_2*x_3-x_0*x
      _4-x_1*x_4+x_2*x_4,x_1*x_2-x_2^2-x_0*x_3+x_2*x_3+x_0*x_4+x_2*x_4+x_4^2,-x_1*x_2-x_2^2-x_0*x_3-x_1*x_3
      +x_2*x_3-x_0*x_4-x_1*x_4-x_3*x_4,x_0*x_1+x_1^2+x_1*x_2+x_0*x_3+x_3^2-x_0*x_4+x_3*x_4,-x_1^2+x_1*x_2+x
      _0*x_3+x_1*x_3-x_3^2+x_1*x_4+x_2*x_4-x_3*x_4+x_4^2,x_1^2+x_1*x_2+x_2*x_3+x_3^2-x_0*x_4-x_3*x_4,-x_0^2
      -x_0*x_1-x_0*x_2+x_0*x_3-x_1*x_3-x_2*x_3-x_3^2+x_0*x_4-x_1*x_4+x_4^2,x_0*x_1-x_0*x_2-x_1*x_3-x_2*x_3-
      x_3^2-x_1*x_4+x_2*x_4+x_4^2,-x_0*x_1-x_0*x_2-x_0*x_3+x_1*x_3-x_2*x_3+x_3^2-x_1*x_4+x_4^2),
      ideal(-x_1*x_2+x_2^2+x_0*x_3-x_1*x_3+x_2*x_3+x_2*x_4-x_3*x_4,-x_0*x_2-x_1*x_2-x_1*x_4+x_2*x_4-x_3*x_4
      +x_4^2,-x_0*x_1-x_1^2-x_1*x_2-x_2*x_3+x_3^2+x_0*x_4-x_2*x_4+x_3*x_4,-x_0*x_1-x_1^2-x_1*x_3+x_3^2-x_0*
      x_4+x_1*x_4,x_1^2-x_1*x_2-x_0*x_3-x_3^2-x_0*x_4-x_1*x_4+x_2*x_4+x_3*x_4,x_0*x_1+x_1^2-x_0*x_3-x_1*x_3
      +x_2*x_3-x_3^2+x_1*x_4+x_3*x_4+x_4^2,x_0^2+x_0*x_1+x_0*x_2-x_0*x_4-x_1*x_4+x_2*x_4-x_3*x_4,x_0^2+x_0*
      x_1+x_0*x_3-x_1*x_3-x_3^2-x_0*x_4-x_1*x_4-x_2*x_4-x_3*x_4,-x_0*x_1+x_0*x_2-x_0*x_3+x_1*x_3+x_1*x_4+x_
      2*x_4+x_3*x_4+x_4^2,-x_0^2-x_0*x_1+x_0*x_3-x_3^2-x_1*x_4+x_3*x_4-x_4^2),
      ideal(x_0*x_2-x_1*x_2+x_2^2-x_0*x_3+x_2*x_3-x_0*x_4+x_2*x_4-x_3*x_4,-x_0*x_2+x_1*x_2-x_2^2+x_1*x_3+x_
      3^2-x_0*x_4+x_1*x_4-x_2*x_4+x_3*x_4-x_4^2,x_0*x_2+x_1*x_2-x_2*x_3+x_0*x_4+x_1*x_4-x_2*x_4+x_4^2,-x_0*
      x_2-x_1*x_2-x_2^2+x_0*x_3+x_0*x_4+x_2*x_4-x_3*x_4+x_4^2,x_0*x_1-x_1^2+x_1*x_2+x_1*x_3-x_2*x_3+x_3^2+x
      _0*x_4-x_1*x_4+x_2*x_4+x_3*x_4+x_4^2,-x_0*x_1-x_1^2+x_0*x_3+x_1*x_3-x_3^2+x_0*x_4-x_1*x_4-x_2*x_4+x_4
      ^2,x_0*x_1+x_1^2+x_1*x_2+x_0*x_3-x_2*x_3-x_1*x_4+x_2*x_4-x_3*x_4+x_4^2,-x_0^2+x_0*x_1-x_0*x_2+x_0*x_3
      +x_1*x_3+x_3^2+x_0*x_4+x_4^2,x_0^2+x_0*x_1+x_3^2-x_2*x_4+x_3*x_4,-x_0^2-x_0*x_1-x_0*x_2-x_0*x_3+x_1*x
      _3+x_3^2-x_0*x_4+x_1*x_4+x_2*x_4-x_3*x_4-x_4^2),
      ideal(-x_0*x_3+x_1*x_3-x_2*x_3+x_3^2-x_0*x_4+x_1*x_4-x_2*x_4,-x_0*x_2+x_1*x_2-x_0*x_3-x_1*x_3-x_2*x_3
      +x_3^2-x_0*x_4+x_2*x_4+x_3*x_4+x_4^2,x_1*x_2+x_1*x_3-x_2*x_3-x_3*x_4,x_0*x_2-x_1*x_2+x_2^2+x_0*x_3-x_
      1*x_3+x_2*x_3+x_3^2+x_0*x_4-x_1*x_4,x_0*x_1-x_1^2+x_0*x_3+x_1*x_3+x_3^2+x_0*x_4+x_1*x_4+x_2*x_4+x_3*x
      _4+x_4^2,-x_1^2+x_1*x_4+x_2*x_4-x_3*x_4-x_4^2,-x_0*x_1+x_1^2-x_1*x_2-x_0*x_3+x_2*x_3+x_3^2-x_1*x_4-x_
      2*x_4+x_3*x_4,-x_0^2+x_0*x_1-x_0*x_3-x_2*x_3+x_3^2+x_0*x_4+x_1*x_4-x_3*x_4-x_4^2,x_0*x_1+x_0*x_3-x_1*
      x_3-x_2*x_3-x_3^2+x_0*x_4+x_1*x_4+x_2*x_4+x_3*x_4+x_4^2,x_0^2-x_0*x_1+x_0*x_2-x_0*x_3+x_1*x_3-x_2*x_3
      -x_3^2+x_1*x_4+x_2*x_4-x_3*x_4-x_4^2),
      ideal(x_1*x_3-x_2*x_3-x_3^2-x_0*x_4-x_3*x_4,x_0*x_2+x_1*x_2+x_2^2+x_0*x_3+x_1*x_3+x_2*x_3+x_0*x_4+x_1
      *x_4+x_3*x_4-x_4^2,-x_0*x_1+x_1^2-x_1*x_2-x_0*x_3+x_2*x_3-x_0*x_4-x_2*x_4-x_3*x_4,-x_0*x_1-x_0*x_3-x_
      2*x_3+x_0*x_4-x_1*x_4-x_2*x_4-x_3*x_4,-x_0*x_3-x_1*x_3+x_2*x_3-x_0*x_4-x_1*x_4+x_2*x_4-x_4^2,-x_0*x_1
      -x_1^2-x_1*x_2-x_0*x_3-x_1*x_3+x_2*x_3+x_3^2-x_0*x_4-x_2*x_4+x_3*x_4+x_4^2,x_0^2-x_0*x_1+x_0*x_2+x_0*
      x_3+x_1*x_3+x_2*x_3-x_0*x_4-x_1*x_4+x_2*x_4+x_3*x_4+x_4^2,x_0^2+x_0*x_3+x_1*x_3+x_3^2+x_0*x_4+x_2*x_4
      +x_3*x_4-x_4^2,-x_0*x_3-x_1*x_3-x_3^2+x_4^2,x_0^2+x_0*x_1+x_0*x_2+x_0*x_3+x_2*x_3+x_0*x_4+x_2*x_4-x_4
      ^2)};

adjTypes={{(4,11,10), 4, (9,19,11), 1, (10,19,10), 0, (9,16,8), 0, (7,11,5)}, {(4,11,10), 5, (9,19,11), 1,
       (10,20,11), 0, (10,20,11), 0, (10,20,11)}, {(4,11,10), 3, (9,19,11), 1, (10,18,9), 2, (8,12,5), 4,
       (4,4,1)}, {(4,11,10), 2, (9,19,11), 3, (10,17,8), 2, (7,10,4), 2, (3,3,1)}, {(4,11,10), 2,
       (9,19,11), 3, (10,17,8), 1, (7,10,4), 8, (3,2,0)}, {(4,11,10), 3, (9,19,11), 2, (10,18,9), 0,
       (8,13,6), 3, (5,6,2)}, {(4,11,10), 0, (9,19,11), 6, (10,15,6), 5, (5,5,1)}};
elapsedTime tally apply(Ms,M->minimalBetti M)
tally adjTypes
--elapsedTime tally (adjTypes=adjointTypes(Ms))  -- 217.792 seconds elapsed

*-




setRandomSeed("8thSurfaceD")
elapsedTime (adjTypes,Ms)=collectSchreyerSurfaces(adjTypes,Ms,P4,1);

tally adjTypes


P4=(ZZ/3)[x_0..x_4]
setRandomSeed("s>2")
Ms={}
setRandomSeed("newSurfacesA")
elapsedTime Ms=collectSchreyerSurfaces(Ms,3,P4,1);

toString Ms
-*
-- Example data for s=3 surfaces --
P4=(ZZ/3)[x_0..x_4]
Ms={ideal(-x_1^2+x_1*x_2+x_1*x_3+x_2*x_3-x_3^2-x_1*x_4-x_3*x_4+x_4^2,x_0*x_1-x_0*x_2+x_0*x_3
      +x_1*x_4-x_2*x_4+x_4^2,-x_2^2-x_0*x_3-x_2*x_3-x_3^2+x_0*x_4-x_1*x_4-x_2*x_4+x_3*x_4+x_4^2
      ,x_2^2+x_1*x_3+x_2*x_4+x_4^2,x_0*x_2-x_1*x_2+x_2^2-x_0*x_3+x_1*x_3-x_2*x_3,x_2^2-x_2*x_3-
      x_1*x_4-x_2*x_4-x_3*x_4-x_4^2,-x_0*x_1+x_1^2-x_1*x_2-x_0*x_3-x_1*x_3-x_2*x_3+x_3^2+x_0*x_
      4+x_3*x_4-x_4^2,-x_1*x_2+x_1*x_3-x_2*x_3+x_3^2+x_1*x_4+x_2*x_4-x_3*x_4,x_0^2-x_0*x_1+x_0*
      x_2+x_1*x_3-x_2*x_3+x_3^2-x_1*x_4-x_2*x_4+x_3*x_4-x_4^2,x_0*x_2+x_0*x_3-x_2*x_3+x_3^2+x_0
      *x_4-x_1*x_4+x_2*x_4-x_4^2),
      ideal(x_0*x_3-x_1*x_3+x_2*x_3-x_0*x_4+x_1*x_4+x_2*x_4+x_3*x_4,-x_0*x_2+x_1*x_2-x_2^2+x_0*
      x_3-x_1*x_3+x_3^2+x_0*x_4-x_1*x_4-x_4^2,-x_1*x_2+x_2^2+x_0*x_3-x_2*x_3+x_3^2-x_0*x_4-x_1*
      x_4+x_2*x_4+x_4^2,-x_0*x_2+x_2^2-x_1*x_3+x_3^2-x_1*x_4-x_2*x_4-x_4^2,x_0*x_1-x_1^2+x_1*x_
      2-x_0*x_3+x_3^2-x_0*x_4+x_3*x_4-x_4^2,x_1^2-x_1*x_2-x_1*x_3-x_2*x_3+x_3^2-x_0*x_4+x_2*x_4
      -x_3*x_4,x_0*x_1-x_1*x_2-x_1*x_3+x_2*x_4-x_4^2,-x_0^2+x_0*x_1-x_0*x_2+x_0*x_3-x_2*x_3-x_3
      ^2+x_0*x_4+x_2*x_4,-x_0*x_1+x_0*x_2-x_0*x_3-x_1*x_3-x_2*x_3-x_1*x_4+x_4^2,-x_0^2+x_0*x_2-
      x_1*x_3-x_3^2-x_0*x_4-x_2*x_4-x_3*x_4),
      ideal(x_2*x_3+x_3^2+x_1*x_4-x_2*x_4-x_3*x_4-x_4^2,-x_0*x_2+x_1*x_2+x_2^2+x_1*x_3-x_2*x_3+
      x_3^2+x_1*x_4+x_2*x_4-x_3*x_4+x_4^2,-x_0*x_2+x_2^2-x_1*x_3-x_1*x_4-x_2*x_4+x_3*x_4+x_4^2,
      x_0*x_2+x_2^2+x_1*x_3+x_2*x_3+x_1*x_4+x_2*x_4,x_0*x_1-x_1^2-x_1*x_2-x_0*x_3+x_1*x_3-x_3^2
      +x_0*x_4+x_3*x_4,x_0*x_1-x_1*x_2+x_0*x_3-x_1*x_3+x_2*x_3+x_3^2+x_0*x_4-x_1*x_4-x_2*x_4,-x
      _0*x_1-x_1*x_2-x_0*x_3-x_2*x_3-x_3^2-x_0*x_4-x_2*x_4-x_3*x_4-x_4^2,-x_0^2+x_0*x_1+x_0*x_2
      +x_0*x_3+x_1*x_3+x_2*x_3-x_3^2-x_0*x_4-x_1*x_4+x_3*x_4,-x_0^2+x_0*x_2-x_0*x_3-x_1*x_3+x_3
      ^2+x_0*x_4-x_2*x_4+x_4^2,x_0^2+x_0*x_2-x_0*x_3+x_1*x_3-x_2*x_3+x_2*x_4+x_3*x_4-x_4^2),
      ideal(x_2^2-x_2*x_3+x_3^2-x_0*x_4+x_2*x_4,x_0*x_2+x_2^2-x_0*x_3+x_2*x_3+x_1*x_4+x_2*x_4-x
      _4^2,x_1^2-x_0*x_3+x_2*x_3+x_3^2-x_0*x_4+x_3*x_4-x_4^2,-x_0*x_1-x_1^2+x_1*x_2+x_0*x_3-x_1
      *x_3+x_2*x_3-x_3^2-x_0*x_4-x_1*x_4+x_2*x_4+x_3*x_4-x_4^2,-x_1*x_2+x_1*x_3-x_0*x_4+x_4^2,-
      x_0*x_1-x_1*x_2-x_0*x_3+x_1*x_3-x_2*x_3-x_0*x_4+x_2*x_4+x_3*x_4-x_4^2,-x_0*x_1+x_1*x_3-x_
      2*x_3+x_3^2-x_0*x_4+x_1*x_4+x_2*x_4-x_4^2,x_0^2+x_0*x_1-x_0*x_2-x_1*x_3-x_3^2-x_0*x_4+x_1
      *x_4-x_2*x_4+x_4^2,x_0*x_2-x_0*x_3+x_1*x_3+x_0*x_4-x_2*x_4+x_4^2,x_0^2+x_0*x_2-x_0*x_3-x_
      1*x_3+x_3^2-x_1*x_4+x_2*x_4-x_4^2)};

tally apply(Ms,M->minimalBetti M)
*-

#Mwith3syzs
elapsedTime tally apply(Mspecial1_{4}, M -> (
	elapsedTime X=schreyerSurfaceFromModule M;
	<< minimalBetti X <<endl;
	elapsedTime (numList,adjList,ptsList,J)=adjunctionProcess(X,4);
	<<numList <<endl;
	<<minimalBetti J <<endl;
	numList))
minimalBetti X
X5=ideal (gens X)_{0..4};
R=X5:X;
dim R, degree R, minimalBetti R
degree(R+X)

minimalBetti J, degree J, dim J
fJ=res J
m2x4=fJ.dd_4^{3..6}
trim ideal m2x4
scroll=ann coker transpose m2x4
minimalBetti scroll
qs=ideal (gens J%scroll)
plane=((ideal(qs_0)+scroll):J)
numList


tex minimalBetti X

-*
Tally{{(4, 11, 10), 2, (9, 19, 11), 2, (10, 17, 8), 4, (7, 9, 3), 7, (2, 1, 0)} => 1 }
            {(4, 11, 10), 2, (9, 19, 11), 3, (10, 17, 8), 1, (7, 10, 4), 8, (3, 2, 0)} => 4
            {(4, 11, 10), 2, (9, 19, 11), 3, (10, 17, 8), 2, (7, 10, 4), 2, (3, 3, 1)} => 1


*-



#Mspecial1

kk=ZZ/2
P4=kk[x_0..x_4],P2=kk[y_0..y_2]
elapsedTime minimalBetti(X=bothmerSurface(P4,P2))
tex minimalBetti X
degree X, genera X
LeBarzN6(11,11,1)
X5=ideal (gens X)_{0..5};
R=X5:X;
dim R, degree R, minimalBetti R
X6=truncate(6,X);
minimalBetti X6
m=syz gens X6;
E=kk[e_0..e_4,SkewCommutative=>true]
M=symExt(m,E);
T=res (coker M,LengthLimit=>8)
betti ((dual T)[-7]**E^{-6})
tex betti ((dual T)[-7]**E^{-6})
elapsedTime (numList,adjList,ptsList,J)=adjunctionProcess(X,2);-- 90.9948 seconds elapsed

numList== {(4, 11, 11), 5, (10, 18, 9), 14, (8, 8, 1)}
minimalBetti J
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


chiITable(13,14),chiITable(13,15), chiITable(12,13)
Ksquare(12,13,2)
LeBarzN6(13,15,1)
(12+9)*2-25

chiITable(14,14),chiITable(14,18)
Ksquare(14,18,1)
LeBarzN6(14,18,1)
(16+9)*2-7*5
chiITable(11,9)
Ksquare(11,9,1)
LeBarzN6(11,9,1)
///
