///
restart
s=2
uninstallPackage "NongeneralTypeSurfacesInP4"

restart
loadPackage ("NongeneralTypeSurfacesInP4")--,Reload=>true)
installPackage("NongeneralTypeSurfacesInP4")--,MakePDF=>true)

viewHelp "NongeneralTypeSurfacesInP4"
check "NongeneralTypeSurfaceInP4"
path 
help adjunctionProcess
///

newPackage(
    "NongeneralTypeSurfacesInP4",
    Version => "0.1",
    Date => "March 28, 2025",
    Headline => "Construction of smooth non-general type surfaces in P4",
    Authors => {
	        { Name => "Hirotachi Abo",Email => "abo@uidaho.edu", HomePage => "https://add"},
	        { Name => "Kristian Ranestad", Email => "ranestad@math.uio.no", HomePage => "https://add"},
	        { Name => "Frank-Olaf Schreyer", Email => "schreyer@math.uni-sb.de", HomePage => "https://www.math.uni-sb.de/ag/schreyer"}},
    AuxiliaryFiles => false,
    DebuggingMode => true,
    PackageExports => {"BGG","AdjunctionForSurfaces"},
    Keywords => {"Algebraic Geometry"}
    )

export {
    --"NongeneralTypeSuracesInP4",
    "sectionalGenus",
    "chiTable",
    "Ksquare",
    "LeBarzN6",
    "cubicScroll",
    "veroneseSurface",
    "delPezzoSurface",
    "castelnuovoSurface",
    "bordigaSurface",
    "ionescuOkonekSurface",
    "degree8OkonekSurface",
    "nonspecialAlexanderSurface",
    "specialityOneAlexanderSurface",
    "degree10pi8RanestadSurface",
    "degree10pi9RanestadSurface",
    "degree10DESSurface",
    "popescuSurface",
    "popescuSurfaces",
    "randomRationalSurface",
    "randomSurfaceDegreeAndSectionalGenus",
    "enriquesSurfaceOfDegree9",
    "enriquesSurfaceOfDegree10",
    "enriquesSurfaceOfDegree11",
    "k3Surfaces",
    "quinticEllipticScroll",
    "horrocksMumfordSurface",
    "ellipticSurface",
    "unirationalFamilies",
    "constructionsViaFiniteFieldSearches",
    "extensionToCharacteristicZero",
    "LabBookProtocol",
    "knownExamples",
    "schreyerSurfaces",
    "schreyerSurface",
    "aboRanestadSurfaces",
    "tateResolutionOfSurface",
    "schreyerSurfaceFromModule",
    "moduleFromSchreyerSurface",
    "exampleOfSchreyerSurfaces",
    "specificSchreyerSurface",
    "findRandomSchreyerSurface",
    "singSchreyerSurfacesStatistic",
    "findRandomSmoothSchreyerSurface",
    "collectSchreyerSurfaces",
    "tangentDimension",
    "schreyerSurfaceWith2LinearSyzygies",
    "unirationalConstructionOfSchreyerSurface",
    "specialEnriquesSchreyerSurface",
    "adjunctionProcessData",
    "prepareAboRanestadSurfaces",
    "aboRanestadSurface",
    "collectSmoothAboRanestadSurfaces",
    "singAboRanestadSurfacesStatistic",
    "aboRanestadSurfaceFromMatrix",
    "matrixFromAboRanestadSurface",
    "tangentComputation",
    "get4x2Matrix",
    "Smooth",
    "Special",
    "KodairaDimension",
    "veroneseImagesInG25",
    "vBELSurface"
}


-* Code section *-
-* numerical functions *-
sectionalGenus=method()
sectionalGenus(Ideal):= X -> (genera X)_1

chiI=method()
chiI(Number,Number,Number) := (m,d,sg) -> binomial(m+4,4)-(binomial(m+1,2)*d-m*(sg-1)+1)



chiITable=method()
chiITable(Number,Number) := (d,sg) -> apply(toList(-1..5),m->chiI(m,d,sg))


Ksquare=method()
-- H2+HK=2(sg-1)
-- d^2-10d-5HK-2K2+12x==0
Ksquare(Number,Number,Number) := (d,sg,xO) -> (HK:=2*(sg-1)-d;
    floor(1/2*(d^2-10*d-5*HK+12*xO)))

LeBarzN6=method()
LeBarzN6(Number,Number,Number) := (d,sg,xO) -> (
    delta:=binomial(d-1,2)-sg;
    t:= binomial(d-1,3)-sg*(d-3)+2*(xO-1);
    h:= floor(1/2*(delta*(delta-d+2)-3*t));
    floor(-1/144*d*(d-4)*(d-5)*(d^3+30*d^2-577*d+786)+
	    delta*(2*binomial(d,4)+2*binomial(d,3)-45*binomial(d,2)+148*d-317)-
	    1/2*binomial(delta,2)*(d^2-27*d+120)-2*binomial(delta,3)+
	    h*(delta-8*d+56)+t*(9*d-3*delta-28)+binomial(t,2))
    )

-* rational surfaces *-
cubicScroll=method()
cubicScroll(PolynomialRing) := P4 -> minors(2,matrix{{P4_0,P4_1,P4_3},{P4_1,P4_2,P4_4}})
///

///
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


castelnuovoSurface=method()
castelnuovoSurface(PolynomialRing) := P4 -> minors(2,random(P4^{-2,2:-3},P4^{2:-4}))

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
    assert(dim X==3 and  degree X==7 and sectionalGenus X==4);
    X)



degree8OkonekSurface=method()

degree8OkonekSurface(PolynomialRing,Ring) :=(P4,E) -> (
    m6x2:=random(E^6,E^{-2,-4});
    betti(T:=res(coker m6x2,LengthLimit=>3));
    X:= saturate ideal syz symExt(T.dd_3,P4);
    assert(dim X==3 and  degree X==8 and  (genera X)_1==6);
    X)


degree8AlexanderSurface=method()
degree8AlexanderSurface(PolynomialRing,PolynomialRing) := (P4,P2) -> (
    H:= intersect (apply(10,i->(ideal random(P2^1,P2^{2:-1}))^2)|{ideal random(P2^1,P2^{2:-1})});
    X:= trim ker map(P2,P4,gens H);
    assert(dim X==3 and degree X==8 and sectionalGenus X==5);
    X)


nonspecialAlexanderSurface=method()
nonspecialAlexanderSurface(PolynomialRing) := P4 -> (
    betti(L :=matrix{{P4_0,P4_1,P4_2}}|random(P4^1,P4^{15:-2}));
    betti(L2 :=map(P4^{3:-1},P4^{3:-1},0)|random(P4^{3:-1},P4^{15:-2}));
    betti (N:=transpose (transpose L| transpose L2));
    betti (fN:=res coker N);
    X:=trim ideal (fN.dd_4*syz fN.dd_4^{16..21});
    assert(dim X==3 and degree X==9 and sectionalGenus X==6);
    X)

enriquesSurfaceOfDegree9=method()
enriquesSurfaceOfDegree9(PolynomialRing) := P4 -> (
    N:=random(P4^1,P4^{12:-2});
    betti (fN:=res coker N);
    X:=trim ideal (fN.dd_4*syz fN.dd_4^{15..20});
    assert(dim X==3 and degree X==9 and sectionalGenus X==6);
    X)

nonspecialAlexanderSurface(PolynomialRing,PolynomialRing) := (P4,P2) -> (
    --tenPts = minors(4,random(P4^5,P4^{4:-1}));
    --elapsedTime betti (h1=saturate (tenPts^4))
    betti(h1:=intersect apply(10,c->(ideal random(P2^1,P2^{2:-1}))^4));
    X:=trim ker map(P2,P4,(gens h1)_{0..4});
    assert(dim X==3 and degree X==9 and sectionalGenus X==6);
    X)


specialityOneAlexanderSurface=method()
specialityOneAlexanderSurface(PolynomialRing,Ring) := (P4,E) -> (
    b1:=gens trim ideal(basis(2,E)%ideal(E_0,E_1))|matrix{{E_0,E_1}};
    bb:=b1||random(E^{1},source b1);
    T:=res(coker bb,LengthLimit=>3);
    X:=trim saturate ideal syz symExt(T.dd_3,P4);
    assert(dim X==3 and degree X== 9 and sectionalGenus X==7);
    X)



degree10pi8RanestadSurface=method()
degree10pi8RanestadSurface(PolynomialRing) := P4 -> (
    a1:=transpose matrix apply (5,i->{P4_i,random(0,P4)*P4_i});
    a2:=map(P4^1,P4^{2:-2},0)||matrix{{sum(3,i->random(0,P4)*P4_i^2),sum(2,i->random(0,P4)*P4_(i+3)^2)}};
    aa:=map(P4^2,,a1|a2);
    faa:=res(coker aa,LengthLimit=>4);
    b1:=faa.dd_3^{0..14}_{0..13};
    m15x5:=syz transpose syz (transpose (b1*random(source b1,P4^{1:-4})),DegreeLimit=>-3);
    X:= trim ideal(transpose (syz transpose (faa.dd_2_{0..14}*m15x5))_{2}*faa.dd_2);
    assert(dim X==3 and degree X==10 and sectionalGenus X==8);
    X)

enriquesSurfaceOfDegree10=method()
enriquesSurfaceOfDegree10(PolynomialRing) := P4 -> (
    a1:=transpose matrix apply (5,i->{P4_i,random(0,P4)*P4_i});
    a2:=map(P4^1,P4^{2:-2},0)||matrix{{sum(3,i->random(0,P4)*P4_i^2),sum(3,i->random(0,P4)*P4_(i+2)^2)}};
    aa:=map(P4^2,,a1|a2);
    faa:=res(coker aa,LengthLimit=>4);
    b1:=faa.dd_3^{0..14}_{0..12};
    m15x5:=syz transpose syz (transpose (b1*random(source b1,P4^{1:-4})),DegreeLimit=>-3);
    X:= trim ideal(transpose (syz transpose (faa.dd_2_{0..14}*m15x5))_{2}*faa.dd_2);
    assert(dim X==3 and degree X==10 and sectionalGenus X==8);
    X)

degree10pi9RanestadSurface=method()
degree10pi9RanestadSurface(PolynomialRing,Ring) := (P4,E) -> (
    a1:=(syz matrix{{E_0,E_1}})*random(E^{3:-1},E^{2:-2});
    a2:=map(E^2,,random(E^2,E^{2:-3})|transpose a1);
    T :=res(coker a2,LengthLimit=>4);
    X := saturate ideal syz symExt(T.dd_4,P4);
    assert(dim X ==3 and degree X==10 and sectionalGenus X==9);
    X)

degree10DESSurface=method()
degree10DESSurface(PolynomialRing,Ring) := (P4,E) -> (
    bb:=random(E^2,E^{2:-2,-3});
    betti (T:= res(coker bb,LengthLimit=>3));
    X := saturate ideal syz symExt(T.dd_3,P4);
    assert(dim X ==3 and degree X==10 and (genera X)_1==9);
    X)


popescuSurface=method()

popescuSurface(PolynomialRing,Ring,Number):= (P4,E,s) -> (
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


randomSurfaceDegreeAndSectionalGenus=method()
randomSurfaceDegreeAndSectionalGenus(Function,List) := (F,ringList) -> (
    (P4,E,P2):=(ringList_0,ringList_1,ringList_2);
    Larg:=toList first methods F;
    arguments :=drop(Larg,1);
    <<endl;
    <<Larg_0; <<endl;
    n:= #arguments; X:=null;
    (if n==1 then X=F(P4) ;
    if n==2 and member(Ring,arguments) then X=F(P4,E);
    if n==2 and not member(Ring,arguments) then X=F(P4,P2)); 
    (d,sg):=(degree X, sectionalGenus X);
    <<minimalBetti X << " cohomology: "<<betti tateResolutionOfSurface X<<endl;
    <<"K2=" <<Ksquare(d,sg,1) <<", N6=" <<LeBarzN6(d,sg,1) <<endl;
    numberOfExceptionalLines:=if d>5 then ((numList,L1,L2,J):=adjunctionProcess(X,1);numList_1) else 0;
    <<"degree="<<d<<", sectional genus="<<sg<<", number of exceptional line=" << numberOfExceptionalLines <<endl;
    {d,sg,numberOfExceptionalLines})

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

-* schreyer surfaces *-

moduleFromSchreyerSurface=method()
moduleFromSchreyerSurface(Ideal) := X -> (
    betti(fX:=res X);
    betti (fN:=res(coker transpose fX.dd_4));
    ideal fN.dd_5)

schreyerSurfaceFromModule=method()
schreyerSurfaceFromModule(Ideal) := M -> (
    P4:= ring M;
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

schreyerSurface=method(Options=>{Smooth=>true,Verbose=>false})
schreyerSurface(Ring,Number) := opt -> (P4,s) -> (
    F:=res(ideal vars P4, LengthLimit=>3);
    kk:=coefficientRing P4;
    M:=null;fM:=null;N:=null;N1:=null; X:=null; singX:=null;
    trials:=1; 
    countSmooth:=1; count:=1; countMonad := 1; countModule := 1; 
    while( --smooth
	while( -- monad ok
	    while( -- module ok
		while ( -- module tested
		    while (-- hilbertFunction ok
			M=ideal (F.dd_3*random(F_3,P4^{-4}));
			apply(4,i->hilbertFunction(i,M))!={1,5,5,0}) do ();
		    fM=res(M,DegreeLimit=>1,LengthLimit=>3);
		    rank fM_3 =!= s) do (countModule=countModule+1);
		while (
		    N1=random(P4^{rank fM_3:-4},P4^{2:-4});
		    coker transpose N1 !=0) do ();
		N = coker transpose (fM.dd_3*N1);
		(dim N , degree N)!=(0,2)) do (countModule=countModule+1);
	    if opt.Verbose then (<<"modules tested = "<<countModule <<endl);
	J1:=syz transpose (fM.dd_2*syz transpose syz(transpose(fM.dd_3*N1),DegreeLimit=>-3));
	source J1 != P4^{0,-2}) do (countMonad=countMonad+1);
	if opt.Verbose then ( <<"monads tested = " << countMonad <<endl);
        X=trim ideal(transpose J1_{1}*syz(fM.dd_1));
	if not opt.Smooth then return X;
	singX= X+minors(2,jacobian X);
	dim saturate singX=!=-1) do (countSmooth=countSmooth+1);
    if opt.Verbose then ( <<"number of surface tested to get a smooth one = " << countSmooth <<endl);
    return X)
///
P4=ZZ/3[x_0..x_4]
2^6,3^6, 5^6
setRandomSeed("repeat")
elapsedTime X=schreyerSurface(P4,3,Verbose=>true);
minimalBetti X
singX=X+minors(2,jacobian X);
dim saturate singX

///

findRandomSchreyerSurface=method()
findRandomSchreyerSurface(Ring) := P4 -> (
    F:=res(ideal vars P4, LengthLimit=>3);
    kk:=coefficientRing P4;
    M:=null;fM:=null;N:=null;N1:=null;J1:=null;
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
    J1=syz transpose (fM.dd_2*syz transpose syz(transpose(fM.dd_3*N1),DegreeLimit=>-3));
    source J1 != P4^{0,-2}) do ();
    trim ideal(transpose J1_{1}*syz(fM.dd_1))
    )

findRandomSchreyerSurface(Ring,Number) := (P4,s) -> (
    F:=res(ideal vars P4, LengthLimit=>3);
    kk:=coefficientRing P4;
    M:=null;fM:=null;N:=null;N1:=null;
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
    Ms:={};L:={};X:=null;M:=null;Rdata:=null;R:=null;
    singX:=null;hypX:=null;X5:=null;
    count:=0;
    while (
	elapsedTime X=findRandomSchreyerSurface(P4);
	M= moduleFromSchreyerSurface(X);
	Ms=append(Ms,M);
	X5=ideal (gens X)_{0..4};
	R=X5:X;
	hypX=X+ideal jacobian X;
	singX=X+minors(2,jacobian X);
	elapsedTime Rdata=(minimalBetti M, dim R, degree R, minimalBetti R,
	    dim singX, degree singX, dim (R+singX));
	<<Rdata<<endl;
	L=append(L,Rdata);
	count=count+1;
	count<N) do ();
    --<<tally L <<endl;
    L)

collectSchreyerSurfaces=method()

collectSchreyerSurfaces(List,List,Number) :=(adjTypes,Ms,N) -> (
    --collect N smooth surfaces
    -- or discover a new family
    P4:= ring first Ms;
    adjTypes1:=adjTypes;Ms1:=Ms;adjTypes2:={};Ms2:={};
    count:=0;count1:=0;
    X:= null; numList:=null; adjList:=null; ptsList:=null;M:= null;J:=null;
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
	<<minimalBetti M <<endl;
	);
    count<1 and count1<N) do ();
    <<tally adjTypes2 <<endl;
    if count==1 then (adjTypes1,Ms1) else (adjTypes2,Ms2)
    )

collectSchreyerSurfaces(List,List,Number,Number) :=(adjTypes,Ms,s,N) -> ( 
    --collect N smooth s>=3 surfaces
    -- or discover a new family
    P4:=ring first Ms;
    adjTypes1:=adjTypes;
    adjTypes2:={};Ms2:={};
    Ms1:=Ms;
    count:=0;count1:=0;
    X:= null; numList:=null; adjList:=null; ptsList:=null;M:= null;J:=null;
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
	<<minimalBetti M <<endl;
	);
    count<1 and count1<N) do ();
    if count==1 then (adjTypes1,Ms1) else (adjTypes2,Ms2)
    )

exampleOfSchreyerSurfaces=method()
exampleOfSchreyerSurfaces(Ring) := P4 -> (
    if char P4 !=3 then error "expected coordinate ring of P4 in caharcteristic 3";
    Ms:={ideal(-P4_0*P4_2+P4_1*P4_2+P4_0*P4_3+P4_2*P4_3-P4_0*P4_4+P4_1*P4_4+P4_2*P4_4-P4_3*P4_4,P4_1*P4
      _2-P4_1*P4_3+P4_2*P4_3-P4_3^2+P4_0*P4_4-P4_1*P4_4+P4_2*P4_4-P4_3*P4_4,P4_0*P4_2-P4_1*P4_2+P4_0
      *P4_3-P4_1*P4_3-P4_0*P4_4-P4_2*P4_4+P4_4^2,-P4_1*P4_2+P4_2^2-P4_0*P4_3+P4_1*P4_3+P4_2*P4_3+P4_
      1*P4_4-P4_2*P4_4+P4_3*P4_4-P4_4^2,-P4_1^2+P4_0*P4_3+P4_3^2-P4_0*P4_4+P4_1*P4_4-P4_2*P4_4+P4_3
      *P4_4,-P4_0*P4_1+P4_1^2-P4_0*P4_3-P4_1*P4_3+P4_3^2+P4_3*P4_4,P4_1^2-P4_1*P4_2-P4_0*P4_3-P4_1*
      P4_3+P4_2*P4_3+P4_3^2-P4_3*P4_4+P4_4^2,P4_0*P4_1-P4_0*P4_3-P4_2*P4_3+P4_3^2-P4_0*P4_4-P4_1*P4_
      4+P4_3*P4_4+P4_4^2,P4_0^2-P4_0*P4_1-P4_0*P4_3-P4_2*P4_3+P4_3^2-P4_0*P4_4-P4_1*P4_4+P4_2*P4_4-
      P4_3*P4_4-P4_4^2,-P4_0*P4_1+P4_0*P4_2-P4_0*P4_3-P4_2*P4_3-P4_0*P4_4+P4_2*P4_4-P4_3*P4_4+P4_4^2
      ), 
      ideal(-P4_2*P4_3+P4_3^2-P4_2*P4_4-P4_3*P4_4+P4_4^2,P4_0*P4_2+P4_1*P4_2+P4_2^2+P4_0*P4_3-P4_
      1*P4_3+P4_3^2+P4_0*P4_4+P4_1*P4_4-P4_2*P4_4-P4_4^2,P4_0*P4_2-P4_1*P4_2+P4_2^2-P4_2*P4_3+P4_3^
      2+P4_0*P4_4-P4_1*P4_4-P4_3*P4_4-P4_4^2,P4_2^2+P4_0*P4_3+P4_1*P4_3-P4_3^2+P4_0*P4_4+P4_1*P4_4+
      P4_2*P4_4+P4_3*P4_4-P4_4^2,-P4_0*P4_1-P4_1^2-P4_1*P4_2+P4_0*P4_3+P4_2*P4_3+P4_3^2+P4_2*P4_4+P4
      _3*P4_4,-P4_0*P4_1+P4_1^2-P4_1*P4_2+P4_0*P4_3-P4_1*P4_3+P4_2*P4_3+P4_3^2-P4_0*P4_4+P4_2*P4_4-
      P4_4^2,-P4_1*P4_2-P4_0*P4_3+P4_1*P4_3-P4_2*P4_3+P4_3^2+P4_0*P4_4-P4_1*P4_4+P4_2*P4_4+P4_4^2,P4
      _0^2+P4_0*P4_1+P4_0*P4_2-P4_0*P4_3-P4_1*P4_3-P4_2*P4_3-P4_3^2-P4_1*P4_4+P4_2*P4_4-P4_3*P4_4-P4
      _4^2,P4_0^2-P4_0*P4_1+P4_0*P4_2-P4_0*P4_3+P4_2*P4_3+P4_3^2+P4_0*P4_4,P4_0*P4_2+P4_0*P4_3-P4_1
      *P4_3+P4_2*P4_3-P4_3^2+P4_0*P4_4+P4_1*P4_4-P4_2*P4_4+P4_3*P4_4+P4_4^2),
      ideal(P4_1*P4_3+P4_2*P4_3-P4_3^2-P4_0*P4_4+P4_1*P4_4,-P4_0*P4_2-P4_1*P4_2-P4_2^2+P4_0*P4_
      3-P4_1*P4_3-P4_2*P4_3-P4_0*P4_4-P4_1*P4_4+P4_2*P4_4,P4_1*P4_2-P4_2^2-P4_0*P4_3+P4_2*P4_3+P4_0*
      P4_4+P4_2*P4_4+P4_4^2,-P4_1*P4_2-P4_2^2-P4_0*P4_3-P4_1*P4_3+P4_2*P4_3-P4_0*P4_4-P4_1*P4_4-P4_3
      *P4_4,P4_0*P4_1+P4_1^2+P4_1*P4_2+P4_0*P4_3+P4_3^2-P4_0*P4_4+P4_3*P4_4,-P4_1^2+P4_1*P4_2+P4_0*
      P4_3+P4_1*P4_3-P4_3^2+P4_1*P4_4+P4_2*P4_4-P4_3*P4_4+P4_4^2,P4_1^2+P4_1*P4_2+P4_2*P4_3+P4_3^2-
      P4_0*P4_4-P4_3*P4_4,-P4_0^2-P4_0*P4_1-P4_0*P4_2+P4_0*P4_3-P4_1*P4_3-P4_2*P4_3-P4_3^2+P4_0*P4_4
      -P4_1*P4_4+P4_4^2,P4_0*P4_1-P4_0*P4_2-P4_1*P4_3-P4_2*P4_3-P4_3^2-P4_1*P4_4+P4_2*P4_4+P4_4^2,-
      P4_0*P4_1-P4_0*P4_2-P4_0*P4_3+P4_1*P4_3-P4_2*P4_3+P4_3^2-P4_1*P4_4+P4_4^2),
      ideal(-P4_0*P4_3+P4_1*P4_3-P4_2*P4_3+P4_3^2-P4_0*P4_4+P4_1*P4_4-P4_2*P4_4,-P4_0*P4_2+P4_1*P4_
      2-P4_0*P4_3-P4_1*P4_3-P4_2*P4_3+P4_3^2-P4_0*P4_4+P4_2*P4_4+P4_3*P4_4+P4_4^2,P4_1*P4_2+P4_1*P4_
      3-P4_2*P4_3-P4_3*P4_4,P4_0*P4_2-P4_1*P4_2+P4_2^2+P4_0*P4_3-P4_1*P4_3+P4_2*P4_3+P4_3^2+P4_0*P4_
      4-P4_1*P4_4,P4_0*P4_1-P4_1^2+P4_0*P4_3+P4_1*P4_3+P4_3^2+P4_0*P4_4+P4_1*P4_4+P4_2*P4_4+P4_3*P4_
      4+P4_4^2,-P4_1^2+P4_1*P4_4+P4_2*P4_4-P4_3*P4_4-P4_4^2,-P4_0*P4_1+P4_1^2-P4_1*P4_2-P4_0*P4_3+
      P4_2*P4_3+P4_3^2-P4_1*P4_4-P4_2*P4_4+P4_3*P4_4,-P4_0^2+P4_0*P4_1-P4_0*P4_3-P4_2*P4_3+P4_3^2+P4
      _0*P4_4+P4_1*P4_4-P4_3*P4_4-P4_4^2,P4_0*P4_1+P4_0*P4_3-P4_1*P4_3-P4_2*P4_3-P4_3^2+P4_0*P4_4+P4
      _1*P4_4+P4_2*P4_4+P4_3*P4_4+P4_4^2,P4_0^2-P4_0*P4_1+P4_0*P4_2-P4_0*P4_3+P4_1*P4_3-P4_2*P4_3-P4
      _3^2+P4_1*P4_4+P4_2*P4_4-P4_3*P4_4-P4_4^2),
      ideal(-P4_1*P4_2+P4_2^2+P4_0*P4_3-P4_1*P4_3+P4_2*P4_3+P4_2*P4_4-P4_3*P4_4,-P4_0*P4_2-P4_1*P4_
      2-P4_1*P4_4+P4_2*P4_4-P4_3*P4_4+P4_4^2,-P4_0*P4_1-P4_1^2-P4_1*P4_2-P4_2*P4_3+P4_3^2+P4_0*P4_4
      -P4_2*P4_4+P4_3*P4_4,-P4_0*P4_1-P4_1^2-P4_1*P4_3+P4_3^2-P4_0*P4_4+P4_1*P4_4,P4_1^2-P4_1*P4_2-
      P4_0*P4_3-P4_3^2-P4_0*P4_4-P4_1*P4_4+P4_2*P4_4+P4_3*P4_4,P4_0*P4_1+P4_1^2-P4_0*P4_3-P4_1*P4_3+
      P4_2*P4_3-P4_3^2+P4_1*P4_4+P4_3*P4_4+P4_4^2,P4_0^2+P4_0*P4_1+P4_0*P4_2-P4_0*P4_4-P4_1*P4_4+P4_
      2*P4_4-P4_3*P4_4,P4_0^2+P4_0*P4_1+P4_0*P4_3-P4_1*P4_3-P4_3^2-P4_0*P4_4-P4_1*P4_4-P4_2*P4_4-P4_
      3*P4_4,-P4_0*P4_1+P4_0*P4_2-P4_0*P4_3+P4_1*P4_3+P4_1*P4_4+P4_2*P4_4+P4_3*P4_4+P4_4^2,-P4_0^2-
      P4_0*P4_1+P4_0*P4_3-P4_3^2-P4_1*P4_4+P4_3*P4_4-P4_4^2),
      ideal(P4_0*P4_2-P4_1*P4_2+P4_2^2-P4_0*P4_3+P4_2*P4_3-P4_0*P4_4+P4_2*P4_4-P4_3*P4_4,-P4_0*P4_2
      +P4_1*P4_2-P4_2^2+P4_1*P4_3+P4_3^2-P4_0*P4_4+P4_1*P4_4-P4_2*P4_4+P4_3*P4_4-P4_4^2,P4_0*P4_2+P4
      _1*P4_2-P4_2*P4_3+P4_0*P4_4+P4_1*P4_4-P4_2*P4_4+P4_4^2,-P4_0*P4_2-P4_1*P4_2-P4_2^2+P4_0*P4_3+
      P4_0*P4_4+P4_2*P4_4-P4_3*P4_4+P4_4^2,P4_0*P4_1-P4_1^2+P4_1*P4_2+P4_1*P4_3-P4_2*P4_3+P4_3^2+P4_
      0*P4_4-P4_1*P4_4+P4_2*P4_4+P4_3*P4_4+P4_4^2,-P4_0*P4_1-P4_1^2+P4_0*P4_3+P4_1*P4_3-P4_3^2+P4_0
      *P4_4-P4_1*P4_4-P4_2*P4_4+P4_4^2,P4_0*P4_1+P4_1^2+P4_1*P4_2+P4_0*P4_3-P4_2*P4_3-P4_1*P4_4+P4_2
      *P4_4-P4_3*P4_4+P4_4^2,-P4_0^2+P4_0*P4_1-P4_0*P4_2+P4_0*P4_3+P4_1*P4_3+P4_3^2+P4_0*P4_4+P4_4^
      2,P4_0^2+P4_0*P4_1+P4_3^2-P4_2*P4_4+P4_3*P4_4,-P4_0^2-P4_0*P4_1-P4_0*P4_2-P4_0*P4_3+P4_1*P4_3
      +P4_3^2-P4_0*P4_4+P4_1*P4_4+P4_2*P4_4-P4_3*P4_4-P4_4^2),
      ideal(-P4_0*P4_2+P4_2^2+P4_1*P4_3+P4_2*P4_3+P4_3^2-P4_1*P4_4+P4_2*P4_4,P4_1*P4_2+P4_2^2+P4_0
      *P4_3-P4_3^2-P4_0*P4_4-P4_1*P4_4-P4_3*P4_4,P4_0*P4_2-P4_1*P4_2+P4_0*P4_3+P4_1*P4_3-P4_3^2+P4_1
      *P4_4+P4_2*P4_4+P4_3*P4_4-P4_4^2,-P4_0*P4_2-P4_1*P4_2+P4_2^2-P4_0*P4_3-P4_2*P4_3+P4_0*P4_4+P4_
      4^2,-P4_1^2-P4_1*P4_2-P4_0*P4_3-P4_1*P4_3-P4_2*P4_3+P4_3^2+P4_2*P4_4,-P4_0*P4_1+P4_1^2+P4_0*
      P4_3-P4_1*P4_3-P4_2*P4_3-P4_3^2-P4_1*P4_4+P4_2*P4_4-P4_4^2,P4_0*P4_1+P4_1^2-P4_1*P4_2+P4_1*P4_
      3-P4_2*P4_3-P4_3^2+P4_3*P4_4-P4_4^2,P4_0*P4_1+P4_0*P4_2+P4_1*P4_3+P4_2*P4_3+P4_3^2-P4_1*P4_4+
      P4_2*P4_4-P4_3*P4_4-P4_4^2,P4_0^2-P4_0*P4_1-P4_0*P4_3+P4_2*P4_3-P4_3^2+P4_0*P4_4-P4_1*P4_4+P4_
      3*P4_4+P4_4^2,-P4_0^2-P4_0*P4_1+P4_0*P4_2+P4_2*P4_3-P4_1*P4_4-P4_2*P4_4+P4_3*P4_4),
      ideal(P4_0*P4_2+P4_0*P4_3-P4_1*P4_3+P4_3^2+P4_0*P4_4-P4_1*P4_4-P4_3*P4_4,-P4_0*P4_2+P4_1*P4_2
      -P4_2^2+P4_1*P4_3+P4_0*P4_4+P4_1*P4_4-P4_2*P4_4+P4_3*P4_4-P4_4^2,-P4_2^2-P4_0*P4_3+P4_1*P4_3-
      P4_2*P4_3-P4_0*P4_4+P4_3*P4_4+P4_4^2,P4_1*P4_2-P4_2^2+P4_0*P4_3-P4_1*P4_3-P4_2*P4_3+P4_3^2+P4_
      0*P4_4-P4_1*P4_4+P4_2*P4_4-P4_4^2,P4_0*P4_1-P4_1^2+P4_1*P4_2-P4_0*P4_3-P4_1*P4_3-P4_2*P4_3-P4_
      0*P4_4-P4_1*P4_4+P4_3*P4_4+P4_4^2,P4_1*P4_2-P4_3^2+P4_0*P4_4-P4_1*P4_4,-P4_1^2+P4_1*P4_2-P4_0
      *P4_3+P4_1*P4_3-P4_2*P4_3+P4_3^2+P4_0*P4_4-P4_1*P4_4-P4_2*P4_4-P4_4^2,-P4_0^2+P4_0*P4_1-P4_0*
      P4_2+P4_0*P4_3+P4_1*P4_3+P4_2*P4_3-P4_3^2-P4_0*P4_4+P4_1*P4_4+P4_2*P4_4-P4_3*P4_4,-P4_0*P4_2+P4
      _0*P4_3+P4_2*P4_3-P4_3^2+P4_0*P4_4+P4_1*P4_4,P4_0*P4_1-P4_0*P4_2-P4_0*P4_3+P4_2*P4_3-P4_3^2+P4
      _1*P4_4), ideal(P4_1*P4_3-P4_2*P4_3-P4_3^2-P4_0*P4_4-P4_3*P4_4,P4_0*P4_2+P4_1*P4_2+P4_2^2+P4
      _0*P4_3+P4_1*P4_3+P4_2*P4_3+P4_0*P4_4+P4_1*P4_4+P4_3*P4_4-P4_4^2,-P4_0*P4_1+P4_1^2-P4_1*P4_2-
      P4_0*P4_3+P4_2*P4_3-P4_0*P4_4-P4_2*P4_4-P4_3*P4_4,-P4_0*P4_1-P4_0*P4_3-P4_2*P4_3+P4_0*P4_4-P4_1
      *P4_4-P4_2*P4_4-P4_3*P4_4,-P4_0*P4_3-P4_1*P4_3+P4_2*P4_3-P4_0*P4_4-P4_1*P4_4+P4_2*P4_4-P4_4^2
      ,-P4_0*P4_1-P4_1^2-P4_1*P4_2-P4_0*P4_3-P4_1*P4_3+P4_2*P4_3+P4_3^2-P4_0*P4_4-P4_2*P4_4+P4_3*P4_
      4+P4_4^2,P4_0^2-P4_0*P4_1+P4_0*P4_2+P4_0*P4_3+P4_1*P4_3+P4_2*P4_3-P4_0*P4_4-P4_1*P4_4+P4_2*P4_
      4+P4_3*P4_4+P4_4^2,P4_0^2+P4_0*P4_3+P4_1*P4_3+P4_3^2+P4_0*P4_4+P4_2*P4_4+P4_3*P4_4-P4_4^2,-P4
      _0*P4_3-P4_1*P4_3-P4_3^2+P4_4^2,P4_0^2+P4_0*P4_1+P4_0*P4_2+P4_0*P4_3+P4_2*P4_3+P4_0*P4_4+P4_2
      *P4_4-P4_4^2)};
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

specificSchreyerSurface=method()
specificSchreyerSurface(Ring,Number) := (P4,k) -> (
    (Ms,Types):=exampleOfSchreyerSurfaces(P4);
    X:=schreyerSurfaceFromModule(Ms_k);
    <<Types_k <<endl;
    X)

///
kk=ZZ/3
P4=kk[x_0..x_4]
setRandomSeed("repeat and good2") --  1096.85 seconds elapsed
setRandomSeed("repeat and good3")  -- 25.7218 seconds elapsed
setRandomSeed("repeat and good4")  -- 13.3464 seconds elapsed

elapsedTime X=specificSchreyerSurface(P4,7);
minimalBetti X
X5=ideal (gens X)_{0..4};
R=X5:X;
dim R, degree R
tally apply(primaryDecomposition R,c->(dim c,degree c, betti c))
planes=select(decompose R,c->dim c==3)
ci=ideal( gens X*random(source gens X, P4^{2:-5}));
betti(Y=(ci:X):R)
minimalBetti Y, degree Y, genera Y
ci2=ideal(gens Y*random(source gens Y,P4^{2:-4}));
Z=ci2:Y;minimalBetti Z
cZ=primaryDecomposition Z
tally apply(cZ,c->(dim c, degree c, minimalBetti c, minimalBetti radical c))
betti(f1=res cZ_1)
f1.dd_2
hypPlane1=ideal cZ_0_0
decompose(cZ_1+hypPlane1)
apply(planes,p->(dim(p+cZ_1),degree(p+cZ_1)))
threePts=apply(planes,p->(pts=p+cZ_1;minimalBetti pts, minimalBetti radical pts))
tally apply(planes,p->(pts=p+cZ_1;
	tally apply(primaryDecomposition pts,c->(degree c ,minimalBetti c, minimalBetti radical c))))
vertex=trim sum planes
///

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
///
kk=ZZ/nextPrime(10^3)
P4=kk[x_0..x_4]
elapsedTime X=unirationalConstructionOfSchreyerSurfaces(P4,KodairaDimension=>-1);
minimalBetti X
M=moduleFromSchreyerSurface X;
minimalBetti M
tangentDimension M
///

schreyerSurfaceWith2LinearSyzygies=method(Options=>{Smooth=>true})
schreyerSurfaceWith2LinearSyzygies(Ring) := opt -> P4 -> (
    m2x3:=matrix{{P4_0,P4_1,P4_3},{P4_1,P4_2,P4_4}};
    scroll:=minors(2,m2x3);
    hypPlane:=ideal P4_1;
    lines1:=decompose(hypPlane+scroll);
    q2x2 := matrix{{P4_0,P4_2}}||random(P4^1,P4^{2:-1})%hypPlane;
    quadric := hypPlane+minors(2,q2x2);
    Z:=intersect(scroll,quadric);
    twoPointsa:=(decompose(quadric+scroll))_{1,2};
    if twoPointsa_0+lines1_0==twoPointsa_0 then twoPointsa=twoPointsa_{1,0};
    twoPointsb:=apply(lines1_{0,1},l->trim(l+lines1_2));
    twoLines:=apply(2,i->ideal (gens intersect(twoPointsa_i,twoPointsb_i))_{0..2});
    vertex:=ideal random(P4^1,P4^{4:-1});
    twoPlanes:=apply(twoLines,l->ideal (gens intersect(l,vertex))_{0,1});
    while( --get four points defined over kk
	middlePlane:=trim sum apply(twoPlanes,p->ideal (gens p*random(source gens p,P4^{-1})));
	betti(conic:=ideal (gens saturate( middlePlane+Z))_{0..2});
	betti(threePoints:=saturate(middlePlane+scroll));
	twoPoints:=apply(2,i->decompose(twoPlanes_i+conic));
    not all(twoPoints,a->#a==2)) do ();
    twoPoints=apply(twoPoints,a->first a);
    -- apply(2,i->degree(twoPlanes_i+Z)==6)
    -- degree(conic+Z)==5
    --betti intersect({conic+Z}|twoPoints)
    planeCubics:=apply(2,i->(p7:=saturate intersect(twoPlanes_i+Z,twoPoints_i);
	    twoPlanes_i+ideal(gens p7*random(source gens p7,P4^{-3}))));
    genus2Curve:=intersect(planeCubics|{conic});
    -- dim genus2Curve, degree genus2Curve, genus genus2Curve
    betti(p17:=saturate(Z+genus2Curve));
    --degree p17, dim p17 -- 17 point
    betti (Z':=intersect(Z,genus2Curve));
    ci2:=ideal(gens Z'*random(source gens Z',P4^{2:-4}));
    Y:=ci2:Z; --betti Y
    unionOfPlanes:=intersect(twoPlanes|{middlePlane});
    -- minimalBetti unionOfPlanes
    betti(Y':=intersect(Y,unionOfPlanes));
    ci:=ideal(gens Y')_{0,1};
    X:=ci:Y';
    assert((dim X, degree X, (genera X)_1) == (3,11,10));
    if opt.Smooth==true then (
	singX:=saturate(X+minors(2,jacobian X));
	<<"dim singX=" <<dim singX << endl;);
    return X;
    )


///
restart
loadPackage ("NongeneralTypeSurfacesInP4")--,Reload=>true)
kk=ZZ/nextPrime 10^3;
P4=kk[x_0..x_4]
elapsedTime X=schreyerSurfaceWith2LinearSyzygies(P4,Smooth=>true);
minimalBetti X
elapsedTime X=schreyerSurfaceWith2LinearSyzygies(P4);
minimalBetti X
///

unirationalConstructionOfSchreyerSurface=method()
unirationalConstructionOfSchreyerSurface(Ring) := P4 -> (
	planes:=apply(5,i->ideal(P4_i,P4_((i+1)%5)));
	ps := intersect planes;
	Ls:=apply(planes,i->i+ideal random(1,P4));
	L:= intersect Ls;
	cub:=ideal(gens L*random(source gens L,P4^{-3}));
	C:=(intersect planes+cub):L;
	betti(fC:=res C);
	M:=ideal fC.dd_4^{1..10}; 
	X:=schreyerSurfaceFromModule M;
	return X )

specialEnriquesSchreyerSurface=method()
specialEnriquesSchreyerSurface(Ring) := P4 -> (
    kk:=coefficientRing P4;
    t:= symbol t;
    P1:=kk[t_0,t_1];
    parametrisierungConic:=matrix{{2*t_0*t_1,-t_0^2,t_1^2}};
    P2:=kk[(gens P4)_{0..2}];
    conic:=ideal(P2_0^2+4*P2_1*P2_2);
    BringCurve:=ideal(P2_0^4*P2_1*P2_2-P2_0^2*P2_1^2*P2_2^2-
	    P2_0*(P2_1^5+P2_2^5)+2*P2_1^3*P2_2^3);
    randomLine:=null;cp:=null;polarLine:=null;cpts:=null;randomPointOnB:=null;
    while (
	while (
	    randomLine=ideal random(P2^1,P2^{-1});
	    cp=decompose(randomLine+BringCurve);
	not(degree first cp==1 and dim first cp ==1)) do ();
        randomPointOnB=transpose syz transpose jacobian first cp;
	polarLine=ideal(randomPointOnB*jacobian conic);
	cpts=decompose sub(polarLine,parametrisierungConic);
	#cpts=!=2 ) do ( );
    --sub(BringCurve,randomPointOnB)
    pts:=apply(cpts, c-> transpose syz transpose jacobian c);
    sigma:= matrix{{P4_4,P4_0,P4_1,P4_2,P4_3}};
    Qs:=apply(pts,c->(sub(c_(0,1),kk))^2*P4_2*P4_3+sub(c_(0,0),kk)*sub(c_(0,1),kk)*P4_0^2-(sub(c_(0,0),kk))^2*P4_1*P4_4);
    q1:=null;
    Es:=apply(Qs,q->(q1=q;ideal apply(5,i->(q1=sub(q1,sigma);q1))));
    --apply(Es,E->minimalBetti E)
    --minimalBetti intersect Es
    M:=sum Es;
    --minimalBetti M
    X:=schreyerSurfaceFromModule M;
    return X)

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
    d:=null;d2:=null;d3:=null;
    m7x2:=sum(50, i-> (d=def1_i;
	betti (d2=d*fM.dd_2//fM.dd_1);
	betti (d3=d2*fM.dd_3//fM.dd_2);
	T_i*sub(d3^{15..19+s}_{0..s-1},T)));
    50-codim ideal leadTerm mingens trim ideal m7x2)

-* Abo-Ranestad surfaces *-

prepareAboRanestadSurfaces=method()
prepareAboRanestadSurfaces(Ring) := P4 -> (
    kk:=coefficientRing P4;
    e:= symbol e;
    E:=kk[e_0..e_4,SkewCommutative=>true];
    m2x3:=matrix{{e_0,e_1,e_3},{e_1,e_2,e_4}};-- random(E^2,E^{3:-1})
    a:= symbol a; b:= symbol b;
    bs:=flatten apply(4,i->flatten apply(2,j->apply(10,k->b_(i,j,k))));
    as:=flatten apply(2,i->flatten apply(3,j->apply(10,k->a_(i,j,k))));
    B:=kk[bs,as];
    ExB:=E**B;
    E2:=sub(basis(2,E),ExB);
    b4x2:=matrix apply(4,i->apply(2,j->sum(10,k->(sub(b_(i,j,k),ExB)*E2_(0,k)))));
    a2x3:=matrix apply(2,i->apply(3,j->sum(10,k->(sub(a_(i,j,k),ExB)*E2_(0,k)))));
    E3:=sub(basis(3,E),ExB);
(E,m2x3,bs,as,B,ExB,E2,b4x2,a2x3,E3))

get4x2Matrix = method(Options=>{Special=>0})
get4x2Matrix(Matrix,Number) := opt -> (m2x3,n) -> (
    -- n desired number of intersection points in G(2,5)
    E:= ring m2x3;
    kk:= coefficientRing E;
    s:=opt.Special; 
    E':= coefficientRing E[(gens E)_{0..2}];
    m2x2:=map(E^2,E^0,0);
    m2:=null;
    scan(s,cc->(while (m2=random(kk^2,kk^2); det m2==0) do ();
	 m2x2=m2x2|map(E^2,,m2*m2x3_{0,1}*random(kk^2,kk^1))));
    if s==2 then m:=min(4-s,max(0,n-4));
    if s==1 then m=min(4-s,n-1);
    if s==0 then m=min(4,n);    
    scan(m,cc-> (
	 while (m2=random(kk^2,kk^2); det m2==0) do ();
	 m2x2=m2x2|map(E^2,,m2*m2x3*random(kk^3,kk^1))));
    m2x4:=m2x2|random(E^2,E^{4-rank source m2x2:-1});
    transpose m2x4);
    
    

///
kk=ZZ/nextPrime 10^3
P4=kk[x_0..x_4]
(E,m2x3,bs,as,B,ExB,E2,b4x2,a2x3,E3)=prepareAboRanestadSurfaces(P4);
n=4
m4x2=get4x2Matrix(m2x3,n,Special=>2)
c=b4x2*sub(m2x3,ExB)+sub(m4x2,ExB)*a2x3;
I=trim ideal sub(contract(E3,flatten c),B);
numgens I==120-n

n=4
m4x2=get4x2Matrix(m2x3,n,Special=>1)
c=b4x2*sub(m2x3,ExB)+sub(m4x2,ExB)*a2x3;
I=trim ideal sub(contract(E3,flatten c),B);
numgens I==120-n

n=4
m4x2=get4x2Matrix(m2x3,n,Special=>0)
c=b4x2*sub(m2x3,ExB)+sub(m4x2,ExB)*a2x3;
I=trim ideal sub(contract(E3,flatten c),B);
numgens I==120-n

///    

aboRanestadSurface=method(Options=>{Verbose=>false,Smooth=>true,Special=>0})
aboRanestadSurface(Ring,Number) := opt -> (P4,n) -> (
    -- Input: P4 ring of P4
    --        n number of -1 lines
    --        n-1 coincides with number of intersection points in G(2,5)
    --        121-n coincides with the number of generators of the ideal I below 
    -- Output: X an ideal of an AR surface,
    --         m4x2 linear matrix over the exterior algebra    
    assert(member(121-n,toList(112..117)));
    kk:= coefficientRing P4;
    (E,m2x3,bs,as,B,ExB,E2,b4x2,a2x3,E3):=prepareAboRanestadSurfaces(P4);
    count:=1;test:=1;
    I:=null;sol:=null;randSol:=null;m4x2:=0;
    b4x2r:=null;bb:=null;test1:=null;test2:=null;T:=null;X:=null;c:=null;
    countSmooth:=1;singX:=null;
    while( --smooth
    while( -- dim X and degree X
	while( -- syz bb and syz transpose bb has the correct number of generators
	    while( -- numgens I correct
		m4x2=get4x2Matrix(m2x3,n-1,Special=>opt.Special);
		c=b4x2*sub(m2x3,ExB)+sub(m4x2,ExB)*a2x3;
		I=trim ideal sub(contract(E3,flatten c),B);
		numgens I =!= 121-n
		) do (count=count+1);
	    sol=vars B%I;
	    randSol=sub(sol,random(kk^1,kk^140));
	    b4x2r=sub(b4x2,vars E|randSol);
	    betti(bb=map(E^4,,m4x2|b4x2r));
	    test1 = degrees source syz bb =={{3}, {3}, {3}, {4}, {4}, {4}, {4}, {4}};
	    test2 = degrees source syz transpose bb=={{2}, {2}, {2}, {2}, {2}, {2}, {2}, {2}, {2}, {2}, {2}, {2}, {2}};
	    not(test1 and test2)
	    ) do (test=test+1;count=count+1);
	if opt.Verbose then (<<"trials so far to get a surface = " <<count <<endl);
	betti(T=res(coker bb, LengthLimit=>4));
	X=saturate ideal syz symExt(T.dd_4,P4);
	not (dim X ==3 and degree X==12)  ) do ();
    if not opt.Smooth then return (X,m4x2);
    singX=X+minors(2,jacobian X);
    dim singX !=0) do (countSmooth=countSmooth+1);
    if opt.Verbose then (<<"trials to get a smooth surface = "<<countSmooth <<endl);
    (X,m4x2))
///
kk=ZZ/11
P4=kk[x_0..x_4]
elapsedTime (X,m4x2)=aboRanestadSurface(P4,8,Special=>2,Verbose=>true);
minimalBetti X
elapsedTime  (L0,L1,L2,J)=adjunctionProcess(X,1);
L0

X5=ideal (gens X)_{0..4};
R=X5:X;
dim R, degree R, minimalBetti R, degree (R+X)

elapsedTime (X,m4x2)=aboRanestadSurface(P4,6,Special=>2,Verbose=>true);
minimalBetti X
elapsedTime  (L0,L1,L2,J)=adjunctionProcess(X,1);
assert(L0_1==6)

X5=ideal (gens X)_{0..4};
R=X5:X;
dim R, degree R, minimalBetti R, degree (R+X)

kk=ZZ/nextPrime 10^3
P4=kk[x_0..x_4]
elapsedTime (X,m4x2)=aboRanestadSurface(P4,6,Special=>2,Verbose=>true);
E=ring m4x2
m42=m4x2%ideal(vars E)_{0,1,2}
betti syz (transpose m42,DegreeLimit=>2)

kk=ZZ/nextPrime 10^3
P4=kk[x_0..x_4]
elapsedTime (X,m4x2)=aboRanestadSurface(P4,4,Special=>1,Verbose=>true);
E=ring m4x2
m42=m4x2%ideal(vars E)_{0,1,2}
betti syz (transpose m42,DegreeLimit=>2)

kk=ZZ/11
P4=kk[x_0..x_4]
setRandomSeed("repeat again 6")
count=0
elapsedTime while(elapsedTime (X,m4x2)=aboRanestadSurface(P4,8,Special=>1,Verbose=>true);
    <<minimalBetti X <<endl;
	E=ring m4x2;
	m42=m4x2%ideal(vars E)_{0,1,2};
	sm24=syz(transpose m42,DegreeLimit=>2);
	<< betti sm24 << endl;
	rank source sm24=!=5 or numgens X==10) do (count=count+1); count

betti syz transpose m42
minimalBetti X
singX=X+minors(2,jacobian X);
dim singX
elapsedTime  (L0,L1,L2,J)=adjunctionProcess(X,3);
L0
L0=={(4, 12, 13), 8, (12, 24, 13), 1, (12, 20, 9), 8, (8, 9, 2)}
minimalBetti J

kk=ZZ/13
P4=kk[x_0..x_4]
elapsedTime (X,m4x2)=aboRanestadSurface(P4,7,Special=>true,Verbose=>true);
minimalBetti X
elapsedTime  (L0,L1,L2,J)=adjunctionProcess(X,3);
L0
minimalBetti J

kk=ZZ/11
P4=kk[x_0..x_4]
setRandomSeed("search")
elapsedTime (X,m4x2)=aboRanestadSurface(P4,8,Verbose=>true);
minimalBetti X
elapsedTime  (L0,L1,L2,J)=adjunctionProcess(X,3);
L0=={(4, 12, 13), 8, (12, 24, 13), 1, (12, 20, 9), 8, (8, 9, 2)}
///

veroneseImagesInG25=method()
veroneseImagesInG25(Matrix) := m4x2 -> (
    E:=ring m4x2;
    m2x3 := matrix{{E_0,E_1,E_3},{E_1,E_2,E_4}};
    kk:=coefficientRing E;
    y:= symbol y;
    P3:=kk[y_0..y_3];
    ExP3:=E**P3;
    ef:=sub(basis(2,E),ExP3);
    a3:=(vars P3)_{0..2};
    a4:=vars P3;
    a3':=sub(a3,ExP3)*sub(transpose m2x3,ExP3);
    paraP2:=sub(contract(ef,a3'_(0,0)*a3'_(0,1)),P3);
    a4':=sub(a4,ExP3)*sub(m4x2,ExP3);
    paraP3:=sub(contract(ef,a4'_(0,0)*a4'_(0,1)),P3);
    p:=symbol p;
    P9:=kk[p_0..p_9];
    g25:=pfaffians(4,genericSkewMatrix(P9,p_0,5));
    veroP2:=ker map(P3,P9,paraP2);
    veroP3:=ker map(P3,P9,paraP3);
    assert(veroP2+g25==veroP2 and veroP3+g25==veroP3);
    pts:=trim(veroP2+veroP3);
    (pts,veroP2,veroP3,g25))
    

aboRanestadSurfaceFromMatrix=method(Options=>{Verbose=>false,Smooth=>true})
aboRanestadSurfaceFromMatrix(Ring,Matrix) := opt -> (P4,m4x2) -> (
    kk:= coefficientRing P4;
    (E,m2x3,bs,as,B,ExB,E2,b4x2,a2x3,E3):=prepareAboRanestadSurfaces(P4);
    m4x2':=sub(m4x2,vars E);
    count:=1;test:=1;
    I:=null;sol:=null;randSol:=null;
    b4x2r:=null;bb:=null;test1:=null;test2:=null;T:=null;X:=null;c:=null;
    countSmooth:=1;singX:=null;
    while( --smooth
    while( -- dim X and degree X
	while( -- syz bb and syz transpose bb has the correct number of generators
	    c=b4x2*sub(m2x3,ExB)+sub(m4x2',ExB)*a2x3;
	    I=trim ideal sub(contract(E3,flatten c),B);
	    sol=vars B%I;
	    randSol=sub(sol,random(kk^1,kk^140));
	    b4x2r=sub(b4x2,vars E|randSol);
	    betti(bb=map(E^4,,m4x2'|b4x2r));
	    test1 = degrees source syz bb =={{3}, {3}, {3}, {4}, {4}, {4}, {4}, {4}};
	    test2 = degrees source syz transpose bb=={{2}, {2}, {2}, {2}, {2}, {2}, {2}, {2}, {2}, {2}, {2}, {2}, {2}};
	    not(test1 and test2)
	    ) do (test=test+1;count=count+1);
	if opt.Verbose then (<<"trials so far to get a surface = " <<count <<endl);
	betti(T=res(coker bb, LengthLimit=>4));
	X=saturate ideal syz symExt(T.dd_4,P4);
	not (dim X ==3 and degree X==12)  ) do ();
    if not opt.Smooth then return X;
    singX=X+minors(2,jacobian X);
    dim singX !=0) do (countSmooth=countSmooth+1);
    if opt.Verbose then (<<"trials to get a smooth surface = "<<countSmooth <<endl);
    X)
///
kk=ZZ/19
P4=kk[x_0..x_4]
setRandomSeed("fairly fast search")
elapsedTime (X,m4x2)=aboRanestadSurface(P4,6,Special=>2,Verbose=>true);
elapsedTime X=aboRanestadSurfaceFromMatrix(P4,m4x2,Verbose=>true);   
m4x2'=matrixFromAboRanestadSurface X
m4x2
assert(minors(2,sub(m4x2,vars P4))==minors(2,sub(m4x2',vars P4)))
///
matrixFromAboRanestadSurface=method()
matrixFromAboRanestadSurface(Ideal) := X -> (
    T:=tateResolutionOfSurface X;
    E:= ring T;
    m4x2:=(T.dd_4_{2,3}**E^{2});
    m4x2)
  

    
collectSmoothAboRanestadSurfaces=method()
collectSmoothAboRanestadSurfaces(Ring,Number,Number) :=(P4,n,N) -> (
    m4x2s:={};Xs:={};adjTypes:={};
    X:=null;m4x2:=null;m2x3:=null;numList:=null;L1:=null;L2:=null;J:=null;
    count:=0;
    scan(N, i-> (
	    elapsedTime (X,m4x2)=aboRanestadSurface(P4,n);
	    elapsedTime (numList,L1,L2,J)=adjunctionProcess(X,4);
	    Xs=append(Xs,X);
	    adjTypes=append(adjTypes,numList);
	    m4x2s=append(m4x2s,m4x2)));
    return (Xs,adjTypes,m4x2s))





-* Documentation section *-


beginDocumentation()


document {
Key => NongeneralTypeSurfacesInP4,
Headline => "Construction of smooth non-general type surfaces in P4",
   "In 1989 Elligsrud and Peskine proved a conjecture of Harstshorne and Lichtenbaum about smooth rational surfaces in P4. In fact, more generally:
    There are only finitely many components of the Hilbert scheme of surfaces in P4, whose general point correspond to a smooth 
    surface not of general type.

   In that period there was a flurish of activities to construct such surfaces, in part using Computer Algebra. In this package we review
   those constructions, which after 30 years of Macaulay2 have become simpler and faster. Moreover we have discovered a few further 
   examples",

   PARA{},
     SUBSECTION "Rational surfaces",
     UL{
	TO randomRationalSurface,
	TO knownExamples,
	TO schreyerSurfaces,
	TO aboRanestadSurfaces
        },
     SUBSECTION "Enriques and K3 surfaces",
     UL{
        TO enriquesSurfaceOfDegree9,
	TO enriquesSurfaceOfDegree10,
	TO k3Surfaces,
        },
    SUBSECTION "Irregular surface",
     UL{
        TO quinticEllipticScroll,
	TO horrocksMumfordSurface,
        },
    SUBSECTION "Elliptic surfaces",
     UL{
        TO quinticEllipticScroll,
        },
     SUBSECTION "Existence proofs",
     UL{
	TO adjunctionProcessData,
	TO unirationalFamilies,
	TO constructionsViaFiniteFieldSearches,
	TO extensionToCharacteristicZero,
	TO LabBookProtocol
        }     
}


document {
Key => schreyerSurfaces,
Headline => "functions concerning Schreyer surfaces",
   "[Schreyer,1996] discovered 4 families of surfaces X in P4 with d=11, sectional genus pi=10 Via a search over a finite field
   of which 3 families consists of rational surfaces, the 
   Repeating such search now, we found altogether 10 families. In the following we give an overview
   of the functions used in that search.",
   
   PARA{},
     SUBSECTION "from modules to surfaces",
     UL{
        TO schreyerSurfaceFromModule,
	TO moduleFromSchreyerSurface,
        TO exampleOfSchreyerSurfaces,
        TO specificSchreyerSurface
        },
    
     SUBSECTION "search for modules",
     UL{
	TO findRandomSchreyerSurface,
        TO singSchreyerSurfacesStatistic,
        TO findRandomSmoothSchreyerSurface, 
        TO collectSchreyerSurfaces
        },
    
     SUBSECTION "lift to characteristic zero",
     UL{
	TO tangentDimension,
        TO unirationalConstructionOfSchreyerSurface,
	TO specialEnriquesSchreyerSurface,
	TO schreyerSurfaceWith2LinearSyzygies
        }        
}



document {
Key => aboRanestadSurfaces,
Headline => "functions concerning Abo-Ranestad surfaces",
   "[Abo-Ranestad,199x] discovered 4 families of rational surfaces X in P4 with d=12, sectional genus pi=13 via a search over a finite field.
    Reviewing their construction we found altogether 9 families. 
    Most of these components are unirational.",
   
   PARA{},
     SUBSECTION "from matrices to surfaces",
     UL{
        TO aboRanestadSurfaceFromMatrix,
	TO matrixFromAboRanestadSurface       
        },
    
     SUBSECTION "search for modules",
     UL{
	TO aboRanestadSurface,
        TO singAboRanestadSurfacesStatistic,
        },
    
     SUBSECTION "lift to characteristic zero",
     UL{
	TO tangentComputation,
	TO veroneseImagesInG25
        }        
}

document {
Key => adjunctionProcessData,
Headline => "explains the output of the function adjunctionProcess",
    "We explain the output of the function adjunctionProcess from the package adjunctionForSurfaces",
help adjunctionProcess,                
}



doc ///
Key
 moduleFromSchreyerSurface
 (moduleFromSchreyerSurface, Ideal)
Headline
 compute the H^1-module of the ideal sheaf of X
Usage
 M = moduleFromSchreyerSurface X
Inputs
 X:Ideal
  of a Schreyer surface in P4
Outputs
 M:Ideal
  the ideal defining the H^1-module of the ideal sheaf of X
Description
  Text
    The H^1-module of a Schreyer surface is a finite length module
    with Hilbert function (1,5,5) with at least two extra syzygies.
  Example
    P4=ZZ/3[x_0..x_4];
    (Ms,Types)=exampleOfSchreyerSurfaces P4;
    tally apply(Ms,M->minimalBetti M)
    X=schreyerSurfaceFromModule Ms_1;
    minimalBetti X
    M=moduleFromSchreyerSurface X;
    minimalBetti M
///

doc ///
Key
 schreyerSurfaceFromModule
 (schreyerSurfaceFromModule, Ideal)
Headline
 compute the H^1-module of the ideal sheaf of X
Usage
 X = schreyerSurfaceFromModule X
Inputs
 M:Ideal
  the ideal defining the H^1-module of the ideal sheaf of X
Outputs
 X:Ideal
  the ideal of a Schreyer surface
Description
  Text
    The H^1-module of a Schreyer surface is a finite length module
    with Hilbert function (1,5,5) with at least two extra syzygies.
  Example
    P4=ZZ/3[x_0..x_4];
    (Ms,Types)=exampleOfSchreyerSurfaces P4;
    tally apply(Ms,M->minimalBetti M)
    X=schreyerSurfaceFromModule Ms_1;
    minimalBetti X
    M=moduleFromSchreyerSurface X;
    minimalBetti M
///




doc ///
Key
 schreyerSurfaceWith2LinearSyzygies
 (schreyerSurfaceWith2LinearSyzygies, Ring)
Headline
 compute a rational Schreyer surface whose H^1-module has 4 extra syzyzgies
Usage
 X = schreyerSurfaceWith2LinearSyzygies(P4)
Inputs
 P4:Ring
  the coordinate ring of P4
Outputs
 X:Ideal
  the ideal of a smooth Schreyer surface
Description
  Text
    The construction is a 2 step liaison construction.
    The desired surface has a residual scheme R=X5:X consisting of the union of 3 planes.
    A general (5,5) complete intersection ci has as residual scheme ci:X=R cup Y with
    Y a surface of degree 11 which lies on two quartics. The (4,4) complete intersection
    ci2 has residual Z=ci2:Y of degree 5 which decomposes in a cubic scroll and a quadric surface
    which intersect along the directrix of the scroll and two non-CM points of Z.
  Example
    kk=ZZ/nextPrime(2*10^3);P4=kk[x_0..x_4];
    X=schreyerSurfaceWith2LinearSyzygies(P4);
    elapsedTime X=schreyerSurfaceWith2LinearSyzygies(P4);
    minimalBetti X
    M=moduleFromSchreyerSurface X;
    minimalBetti M
    X5=ideal (gens X)_{0..4};
    R=X5:X;
    minimalBetti radical R
    tally apply(decompose R,c->(dim c, degree c, minimalBetti c))
    ci=ideal( gens X*random(source gens X,P4^{2:-5}));
    Y=(ci:X):R;
    degree Y,betti(fY=res Y)
    nCM=decompose ann coker transpose fY.dd_3
    ci2=ideal (gens Y)_{0,1};
    Z=ci2:Y;
    minimalBetti Z
    cZ=decompose Z;
    tally apply(cZ,c->(dim c, degree c, minimalBetti c))
  Text
    The construction is a reversal of this linkage. Note that both Y and Z are not Cohen-Macaulay
    in two (common) points.     
  Example    
    intersectionOftheTwoComponentsOfZ=sum(cZ);
    apply(cI=decompose intersectionOftheTwoComponentsOfZ,c->(dim c, degree c))
    cI, cI_{1,2}==nCM
    planes=decompose R
    matrix apply(planes,p2->apply(nCM,p->dim(p2+p)))
    matrix apply(planes,p2->apply(planes,p2'->dim(p2+p2')))
    dim(radical R+Z),degree(radical R+Z)
    matrix apply(planes,p2->apply(cZ,c->degree(p2+c)))
    m3x2=(res cZ_1).dd_2
    syz transpose (m3x2%cI_0) -- => cI_0 is the directrix of the scroll
///

doc ///
Key
 unirationalConstructionOfSchreyerSurface
 (unirationalConstructionOfSchreyerSurface, Ring)
Headline
 compute a rational Schreyer surface whose H^1-module has 5 extra syzyzgies
Usage
 X = unirationalConstructionOfSchreyerSurface P4
Inputs
 P4:Ring
  the coordinate ring of P4
Outputs
 X:Ideal
  the ideal of a smooth Schreyer surface
Description
  Text
    The desired surface has a residual scheme R=X5:X consisting of the union of 5 planes.
  Example
    kk=ZZ/nextPrime 10^3;
    P4=kk[x_0..x_4];
    X=unirationalConstructionOfSchreyerSurface(P4);
    minimalBetti X
    M=moduleFromSchreyerSurface X;
    minimalBetti M
    X5=ideal (gens X)_{0..4};
    R=X5:X;
    minimalBetti R
    planes=decompose R
    tangentDimension M
    tally apply(planes,p->tally apply(decompose(p+X),c->(dim c, degree c, betti c)))
    sixSecants1=apply(planes,p-> ideal (gens intersect drop(select(decompose(p+X),c->dim c==1),1))_{0,1,2});
    sixSecants2=apply(5,i->trim (planes_i+planes_((i+1)%5)));
    sixSecants=sixSecants1|sixSecants2
    tally apply(sixSecants, l-> (betti l,dim l, degree (l+X)))
    LeBarzN6(11,10,1)==10
  Text
    Each of the five planes intersects X in a plane quartic curve and three points.
    The sixSecants are the five intersection lines of the planes and the five lines spanned by two of
    the special points in each plane.
///


///
LeBarzN6(11,10,1)
    kk=ZZ/nextPrime 10^3;
    P4=kk[x_0..x_4];
    planes:=apply(5,i->ideal(P4_i,P4_((i+1)%5)));
    ps := intersect planes;
    Ls:=apply(planes,i->i+ideal random(1,P4)); --10 param = P2^5
    L:= intersect Ls;minimalBetti L, dim L, degree L, genus L
    cub:=ideal(gens L*random(source gens L,P4^{-3}));-- P9 of choices for cub
    C:=(intersect planes+cub):L;
    minimalBetti C,dim C, degree C, genus C
    netList (cC=decompose C)
    betti(fC:=res C)
    M:=ideal fC.dd_4^{1..10};
    cub1:=ideal(gens L*random(source gens L,P4^{-3}));-- P9 of choices for cub
    C1:=(intersect planes+cub1):L;
    minimalBetti (intersect planes+cub)
    betti(fC1:=res C1)
    M1:=ideal fC1.dd_4^{1..10};
    M==M1 -- => M does not depend on the choice of cub
    betti (A=saturate ann(coker fC.dd_2^{6..10}_{5..19}))
    minimalBetti A
    minimalBetti coker fC.dd_2^{6..10}_{5..19} -- direct sum of 5 lines
    tangentDimension M, 10+25-5
    X=schreyerSurfaceFromModule M;  10+24-4+2*3
    minimalBetti X
    X5=ideal (gens X)_{0..4};
    R=X5:X;
    minimalBetti R
    cR=decompose R
    tally apply(cR,p->tally apply(decompose(p+X),c->(dim c, degree c)))
    netList cC
    netList apply(planes,p->(p,select(decompose(p+X),c->dim c==1)))
    netList (sixSecants1=apply(planes,p-> ideal (gens intersect drop(select(decompose(p+X),c->dim c==1),1))_{0,1,2}))
    netList unique (apply(Ls,L->trim L)|decompose A)
    netList (sixSecants2=apply(planes,p-> ideal (gens intersect(select(decompose(p+X),c->dim c==1))_{0,1})_{0,1,2}))
    sixSecants3=apply(5,i->trim (planes_i+planes_((i+1)%5)))
    sixSecants=sixSecants1|sixSecants2
    tally apply(sixSecants, l-> (dim l, degree (l+X)))
///



doc ///
Key
 specialEnriquesSchreyerSurface
 (specialEnriquesSchreyerSurface, Ring)
Headline
 compute a Enriques Schreyer surface whose H^1-module has 5 extra syzyzgies
Usage
 X = specialEnriquesSchreyerSurface P4
Inputs
 P4:Ring
  the coordinate ring of P4
Outputs
 X:Ideal
  the ideal of a smooth Schreyer surface
Description
  Text
    The desired surface has a residual scheme R=X5:X which is a quintic elliptic scroll.
    The H^1-module is defined by the sum of the ideals of two elliptic curves on the scroll.
    Thus the construction needs a point p on the Bring curve and the two points on the conic of
    elliptic normal curves of degree 5. Over a finite field such data are easily found by a random search, whose running time
    is independent of the finite ground field
    The two points on the conic are the intersection of the conic with the polar line to the point p of the conic, [Hulek,199x].
    The rest of the construction is unirational.
  Example
    kk=ZZ/nextPrime 10^3;
    P4=kk[x_0..x_4];
    X=specialEnriquesSchreyerSurface(P4);
    minimalBetti X
    M=moduleFromSchreyerSurface X;
    minimalBetti M
    X5=ideal (gens X)_{0..4};
    R=X5:X;
    minimalBetti R
    tangentDimension M==25
  Text
    => these surfaces do not form a complete family
///

///
kk=ZZ/nextPrime 10^3;
P4=kk[x_0..x_4]
elapsedTime X=specialEnriquesSchreyerSurface(P4);
X5=ideal (gens X)_{0..4};
R=X5:X;
minimalBetti R
M=moduleFromSchreyerSurface X;minimalBetti M
fM=res M
m5x15=(transpose fM.dd_3_{0..4}^{0..14})**P4^{-5};
fm5x15=res coker m5x15
betti fm5x15
isIsomorphic(coker m5x15,coker transpose fm5x15.dd_3)
-- => m5x15 is the presentation matrix of the module of global sections of a 2-torsion bundle in E3
E3=ann coker m5x15;
minimalBetti E3
minimalBetti E3

E3+R==E3
cub=ideal(gens E3*random(source gens E3,P4^{-3}));
betti(A=R+cub:E3); dim A, degree A, genus A
betti saturate A
singA=A+minors(3,jacobian A);
saturate singA

elapsedTime cA=decompose A;
apply(decompose(R+quad),c->(dim c, degree c ,genus c))
elapsedTime X=specialEnriquesSchreyerSurface(P4);
betti(fX=res(X,LengthLimit=>2))
elapsedTime betti(N=Hom(module X,P4^1/X)) -- 362.604 seconds elapsed

--phis={homomorphism (N_{4})};
phis=apply(toList(5..16),i->homomorphism N_{i});
As=apply(phis,phi->matrix{apply(15,i->lift(phi_(0,i),P4))});
Bs1=apply(As,A->A*fX.dd_2//fX.dd_1);
betti Bs_1
Bs=apply(Bs1,B->B^{5..14}_{0..2})
T=kk[t_0..t_(#Bs-1)]
m10x3=sum(#Bs,i->t_i*sub(Bs_i,kk))
betti(J2=minors(2,m10x3))
betti(saturate J2)
betti(J=minors(3,m10x3))
codim J ==10-3+1
dim J

P4xT=P4**T
betti(A=sum(#As,i->P4xT_(5+i)*sub(As_i,P4xT)))
betti(B=sum(#Bs1,i->P4xT_(5+i)*sub(Bs1_i,P4xT)))
betti(I=ideal(A*B))
b6=sub(basis(6,P4),P4xT)
betti (I1 =trim ideal sub(contract(b6,gens I),T))
b7=sub(basis(7,P4),P4xT)
betti (I2 =trim ideal sub(contract(b7,gens I),T))
betti trim (I1+I2)
dim I1
betti basis(2,T)
binomial(13,2)
///

doc ///
Key
 specificSchreyerSurface
 (specificSchreyerSurface, Ring, Number)
Headline
 compute a smooth Schreyer surface with given H^1-module
Usage
 X = specificSchreyerSurface(P4,k)
Inputs
 P4:Ideal
  coordinate ring of P4 over a ground field of characteristic 3
 k: Number
  a number between 0 and 9 specifying the specific H^1-module to use. 
Outputs
 X:Ideal
  ideal of a Schreyer surface
Description
  Text
    The function returns one of ten specific smooth schreyer surfaces.
    It prints the corresponding adjunction process data.
    The corresponding H^1-module are precomputed and stored in the function exampleOfSchreyerSurfaces.
  Example
    P4=ZZ/3[x_0..x_4];
    X=specificSchreyerSurface(P4,1);
    minimalBetti X
    M=moduleFromSchreyerSurface X;
    minimalBetti M
SeeAlso
   exampleOfSchreyerSurfaces
///



doc ///
Key
 exampleOfSchreyerSurfaces
 (exampleOfSchreyerSurfaces, Ring)
Headline
 read the list of precomputed H^1-modules of Schreyer surfaces
Usage
 (Ms,types)= exampleOfSchreyerSurfaces P4
Inputs
 P4:Ideal
  coordinate ring of P4 over a ground field of characteristic 3
Outputs
 Ms:List
  of H^1-modules of Schreyer surfaces
 types:List
  of precomputed adjunction type data of the corresponding surfaces 
Description
  Text
    The function reads lists of precomputed H^1-modules and adjunction types
  Example
    P4=ZZ/3[x_0..x_4];
    (Ms,types)=exampleOfSchreyerSurfaces P4;
    tally apply(Ms,M->minimalBetti M)
    netList apply(#Ms,i->(minimalBetti Ms_i, types_i))
///

doc ///
Key
 schreyerSurface
 (schreyerSurface, Ring, Number)
Headline
 find a random Schreyer surface
Usage
 X = schreyerSurface(P4,s)
Inputs
 P4:Ideal
  coordinate ring of P4 over a ground field of characteristic 3
 s:Number
  the number of desired extra syzygies
Outputs
 X:Ideal
  the ideal of a  Schreyer surface 
Description
  Text
    It searches for a suitable H^1-module with Hilbert function (1,5,5) and s >1 extra syzygies by searching in the
    codimension 6+2(s-2) subspace of modules with one extra syzygy, and computes the corresponding surface.
    To find an example one has to check about 3^6 examples of modules.
  Example
    P4=ZZ/3[x_0..x_4];
    setRandomSeed("find one fairly fast");
    elapsedTime X=schreyerSurface(P4,2,Smooth=>false,Verbose=>true);  
    minimalBetti X
    M=moduleFromSchreyerSurface X;
    minimalBetti M

    setRandomSeed("also fairly fast");
    elapsedTime X=schreyerSurface(P4,3,Smooth=>false);  
    minimalBetti X
    M=moduleFromSchreyerSurface X;
    minimalBetti M
SeeAlso
   findRandomSmoothSchreyerSurface
///


doc ///
Key
 findRandomSchreyerSurface
 (findRandomSchreyerSurface, Ring)
 (findRandomSchreyerSurface, Ring, Number)
Headline
 find a random Schreyer surface
Usage
 X = findRandomSchreyerSurface P4
 X = findRandomSchreyerSurface(P4,s)
Inputs
 P4:Ideal
  coordinate ring of P4 over a ground field of characteristic 3
 s:Number
  the number of desired extra syzygies
Outputs
 X:Ideal
  the ideal of a possibly singular Schreyer surface 
Description
  Text
    It searches for a suitable H^1-module with Hilbert function (1,5,5) and two extra syzygies by searching in the
    codimension 6 subspace of modules with one extra syzygy, and computes the corresponding surface.
    To find an example one has to check about 3^6 examples of modules.
  Example
    P4=ZZ/3[x_0..x_4];
    setRandomSeed("find one fairly fast");
    elapsedTime X=findRandomSchreyerSurface P4;  
    minimalBetti X
    M=moduleFromSchreyerSurface X;
    minimalBetti M

    setRandomSeed("also fairly fast");
    elapsedTime X=findRandomSchreyerSurface(P4,3);  
    minimalBetti X
    M=moduleFromSchreyerSurface X;
    minimalBetti M
SeeAlso
   findRandomSmoothSchreyerSurface
///

doc ///
Key
 findRandomSmoothSchreyerSurface
 (findRandomSmoothSchreyerSurface, Ring)
 (findRandomSmoothSchreyerSurface, Ring, Number)
Headline
 find a random smooth Schreyer surface
Usage
 X = findRandomSmoothSchreyerSurface P4
 X = findRandomSmoothSchreyerSurface(P4,s)
Inputs
 P4:Ring
  the coordinate ring of P4 over a ground field of characteristic 3 (or other small prime fields)
 s:Number
  the number of desired extra syzygies
Outputs
 X:Ideal
  the ideal of a smooth Schreyer surface
Description
  Text
    It searches for a suitable H^1-module with Hilbert function (1,5,5) and min(2,s) extra syzygies by searching in the
    codimension 6 subspace of modules with one extra syzygy, and computes the corresponding surface
    and checks it smoothness. Since many H^1-modules lead to singular surfaces one has to check
    more then 3^6 examples of modules.
  Example
    P4=ZZ/3[x_0..x_4];
    setRandomSeed("carefully choosen good randomSeed ");
    elapsedTime X=findRandomSmoothSchreyerSurface(P4,Verbose=>false);  
    minimalBetti X
    singX=X+minors(2,jacobian X);
    dim saturate singX==-1
SeeAlso
   findRandomSchreyerSurface
///

doc ///
Key
 tangentDimension
 (tangentDimension, Ideal)
Headline
 compute the dimension of the tangent space of the strata with s extra syzygies at the point M
Usage
 d=tangentDimension M

Inputs
 M:Ideal
  ideal defining a H^1-module with Hilbert function (1,5,5) with s extra syzygies
Outputs
 d:Number
  dimension of the tangent space of the correponding strata at the given point M
Description
  Text
    To prove the existence of a lift of the corresponding surface to characteristic 0,
    it suffices to prove that the tangent space
    has dimension d=36-dim G(2,s)=36-2*(s-2).
  Example
    P4=ZZ/3[x_0..x_4];
    (Ms,types)=exampleOfSchreyerSurfaces P4;
    --tally apply(Ms,M->minimalBetti M)
    --tally apply(Ms, M->tangentDimension M)
    elapsedTime netList apply(Ms,M->(minimalBetti M, tangentDimension M))
    --elapsedTime Xs=apply(Ms,M->schreyerSurfaceFromModule M);
    --tally apply(Xs,X -> (singX=X+minors(2,jacobian X); dim saturate sing X)
  Text
    This proves that the surfaces precomputed Via exampleOfSchreyerSurfaces
    all lift to smooth surfaces over some algebraic number field (of characteristic 0).
///

doc ///
Key
 veroneseImagesInG25
 (veroneseImagesInG25, Matrix)
Headline
 compute the Veronese images of P2 and P3 in the Grassamnnain G25 and their intersection 
Usage
 (pts,vP2,vP3,g25) = veroneseImagesInG25(m4x2)
Inputs
 m4x2: Matrix
  the 4x2 matrix of linear forms over the exterior algebra
Outputs
 pts:Ideal
  the intersection points of the two Veronese images
 vP2:Ideal
  the ideal of the veronese surface
 vP3:Ideal
  the ideal of the veronese 3-fold
 g25:Ideal
  the ideal of the Grassmannian G(2,5) in P9.
Description
  Text
    It the Tate resolution of an Abo-Ranestad surface their are a 4x2 matrix m4x2 and a 2x3 matrix m2x3
    with linear entries over the exterior algbra. These matrices define rational maps P3 -> G(2,5) and P2 -> G(2,5)
    and the type of the surface depends on how these images intersect in the Grassmannin G(2,5). It turns out that the number of
    (-1) lines on the surface will coincides with the number of intersection points of the images + 1.
    This function verifies this assertion in an example.
  Example
    kk=ZZ/nextPrime 10^3; P4:=kk[x_0..x_4];
    n=7;
    elapsedTime (X,m4x2) = aboRanestadSurface(P4,n,Special=>2);
    (pts,vP2,vP3,g25)=veroneseImagesInG25(m4x2);
    (degree pts,degree vP2,degree vP3,degree g25)
    degree pts==n-1
    "(L0,L1,L2,J)=adjunctionProcess(X,1);";
    "L0_1==n and degree pts==n-1";
    
  
SeeAlso
   adjunctionProcessData
   aboRanestadSurface
///



doc ///
Key
 aboRanestadSurface
 (aboRanestadSurface, Ring, Number)
Headline
 find a random Abo-Ranestad  surface
Usage
 (X,m4x2) = aboRanestadSurface(P4,n)
Inputs
 P4:Ring
  the coordinate ring of P4
 n:Number
  the number of desired (-1) lines on the surface
Outputs
 X:Ideal
  the ideal of a Abo-Ranestad surface
 m4x2:Matrix
  a 4x2 matrix with linear entries over the exterior algebra
Description
  Text
    It the Tate resolution of an Abo-Ranestad surface their are a 4x2 matrix m4x2 and a 2x3 matrix m2x3
    with linear entries over the exterior algbra. These matrices define rational maps P3 -> G(2,5) and P2 -> G(2,5)
    and the type of the surface depends on how these images intersect in the Grassmannin G(2,5). It turns out that the number of
    (-1) lines on the surface will coincides with the number of intersection points of the images + 1.
    We need at least 3 intersection points and can have up to 7 intersection points.
    In the construction we normalize the matrix m2x3 as indicated below
  Example
    kk=ZZ/nextPrime 10^3; e=symbol e; E=kk[e_0..e_4,SkewCommutative=>true];
    m2x3=matrix{{e_0,e_1,e_3},{e_1,e_2,e_4}}
  Text
    One can easily force 3 or 4 intersection points. To find more we perform a random search over
    a finite ground field FF_q. Since an extra intersection point is a codimension 1 condition we can find
    examples with c additional intersection points with about q^c trials.
  Example
    P4=ZZ/nextPrime 10^3[x_0..x_4];
    elapsedTime (X,m4x2)=aboRanestadSurface(P4,5);  
    minimalBetti X
    singX=X+minors(2,jacobian X);
    dim saturate singX==-1
    elapsedTime betti (T=tateResolutionOfSurface X)
    "elapsedTime (numList,L1,L2,J)=adjunctionProcess(X,3);";
    "numList=={(4, 12, 13), 4, (12, 24, 13), 12, (12, 16, 5), 0, (4, 4, 1)}";
  Text
    A special situation occurs when the 4x2 matrix m4x2 contains a 2x2 submatrix with entries in e_0..e_2 as well.
    In that case we have two conics in the e_0..e_2 plane which intersect in 4 points, hence four intersction points in the Grassmannian G(2,5).
    We can fource 2 more intersection points easily and can get a 7-th intersection point by a
    codimension 1 random search.
  Example
    elapsedTime (X,m4x2)=aboRanestadSurface(P4,7,Special=>2);  
    minimalBetti X
    "elapsedTime (numList,L1,L2,J)=adjunctionProcess(X,3);";
    "numList=={(4, 12, 13), 5, (12, 24, 13), 9, (12, 17, 6), 3, (5, 5, 1)}";
    kk=ZZ/19;P4=kk[x_0..x_4];
    setRandomSeed("fast search");
    elapsedTime (X,m4x2)=aboRanestadSurface(P4,6,Special=>0,Verbose=>true);
    minimalBetti X
    "elapsedTime (numList,L1,L2,J)=adjunctionProcess(X,3);";
    "numList=={(4, 12, 13), 6, (12, 24, 13), 6, (12, 18, 7), 6, (6, 6, 1)}";
    setRandomSeed("another fast search");
    elapsedTime (X,m4x2)=aboRanestadSurface(P4,8,Special=>2,Verbose=>true); 
    minimalBetti X
    "elapsedTime (L0,L1,L2,J)=adjunctionProcess(X,3);";
    "L0=={(4, 12, 13), 7, (12, 24, 13), 4, (12, 19, 8), 5, (7, 8, 2)}";
SeeAlso
   adjunctionProcessData
///

doc ///
Key
 matrixFromAboRanestadSurface
 (matrixFromAboRanestadSurface, Ideal)
Headline
 get the 4x2 matix of an Abo-Ranestad surface
Usage
  m4x2 = matrixFromAboRanestadSurface X
Inputs
 X:Ideal
  the ideal of a Abo-Ranestad surface
Outputs
 m4x2:Matrix
  a 4x2 matrix with linear entries over the exterior algebra
Description
  Text
    It the Tate resolution of an Abo-Ranestad surface their are a 4x2 matrix m4x2 and a 2x3 matrix m2x3
    with linear entries over the exterior algbra. The 2x3 matrix is normalized. The function returns the
    4x2 matix.
  Example
    kk=ZZ/19
    P4=kk[x_0..x_4]
    setRandomSeed("fairly fast search")
    elapsedTime (X,m4x2)=aboRanestadSurface(P4,6,Special=>2,Verbose=>true);
    betti tateResolutionOfSurface X
    elapsedTime X=aboRanestadSurfaceFromMatrix(P4,m4x2,Verbose=>true);   
    m4x2'=matrixFromAboRanestadSurface X
    m4x2
    assert(minors(2,sub(m4x2,vars P4))==minors(2,sub(m4x2',vars P4)))
SeeAlso
   aboRanestadSurface
   aboRanestadSurfaceFromMatrix
///

doc ///
Key
 aboRanestadSurfaceFromMatrix
 (aboRanestadSurfaceFromMatrix, Ring, Matrix)
Headline
 get an Abo-Ranestad surface with given 4x2 matrix.
Usage
 X = aboRanestadSurfaceFromMatrix(P4,m4x2)
Inputs
 P4:Ring
  the coordinate ring of P4
 m4x2:Matrix
  a 4x2 matrix with linear entries over the exterior algebra
Outputs
 X:Ideal
  the ideal of a Abo-Ranestad surface
Description
  Text
    It the Tate resolution of an Abo-Ranestad surface their are a 4x2 matrix m4x2 and a 2x3 matrix m2x3
    with linear entries over the exterior algbra. These matrices define rational maps P3 -> G(2,5) and P2 -> G(2,5)
    and the type of the surface depends on how these images intersect in the Grassmannin G(2,5). It turns out that the number of
    (-1) lines on the surface will coincides with the number of intersection points of the images + 1.
    The function returns a corresponding surface X.
  Example
    kk=ZZ/19
    P4=kk[x_0..x_4]
    setRandomSeed("fairly fast search")
    elapsedTime (X,m4x2)=aboRanestadSurface(P4,6,Special=>2,Verbose=>true);
    betti tateResolutionOfSurface X
    elapsedTime X=aboRanestadSurfaceFromMatrix(P4,m4x2,Verbose=>true);   
    m4x2'=matrixFromAboRanestadSurface X
    m4x2
    assert(minors(2,sub(m4x2,vars P4))==minors(2,sub(m4x2',vars P4)))
SeeAlso
   aboRanestadSurface
   matrixFromAboRanestadSurface
///


doc ///
Key
 cubicScroll
 (cubicScroll, PolynomialRing)
Headline
 construct the cubic scroll
Usage
 X= cubicScroll P4
Inputs
 P4:PolynomialRing
  coordinate ring of P4
Outputs
 X:Ideal
  of the cubic scroll in P4
Description
  Text
    The smooth cubic scroll is uniquely determined up to projectivities.
    It is define by the 2x2 minors a 2x3 matrix.
    The function returns this ideal
  Example
    kk=ZZ/nextPrime 10^3;
    P4=kk[x_0..x_4];
    X=cubicScroll P4
    minimalBetti X
///

doc ///
Key
 bordigaSurface
 (bordigaSurface, PolynomialRing)
Headline
 construct a Bordiga surface
Usage
 X= bordigaSurface P4
Inputs
 P4:PolynomialRing
  coordinate ring of P4
Outputs
 X:Ideal
  of the Bordiga surface in P4
Description
  Text
    Constructs a Bordiga surface via its Hilbert-Burch matrix
  Example
    kk=ZZ/nextPrime 10^3;
    P4=kk[x_0..x_4];
    minimalBetti(X=bordigaSurface P4)
///

doc ///
Key
 veroneseSurface
 (veroneseSurface, PolynomialRing, PolynomialRing)
Headline
 construct the Veronese surface
Usage
 X= veroneseSurface(P4,P2)
Inputs
 P4:PolynomialRing
  coordinate ring of P4
Outputs
 X:Ideal
  of the Veronese surface in P4
Description
  Text
    We compute the image from the parameterization.
  Example
    kk=ZZ/nextPrime 10^3;
    P4=kk[x_0..x_4];
    P2=kk[y_0..y_2]
    minimalBetti(X=veroneseSurface(P4,P2))
///

doc ///
Key
 delPezzoSurface
 (delPezzoSurface, PolynomialRing)
Headline
 construct the del Pezzo surface
Usage
 X= delPezzoSurface P4
Inputs
 P4:PolynomialRing
  coordinate ring of P4
Outputs
 X:Ideal
  of the cubic scroll in P4
Description
  Text
    We choose randomly two quadrics.
  Example
    kk=ZZ/nextPrime 10^3;
    P4=kk[x_0..x_4];
    minimalBetti(X=delPezzoSurface P4)
///

doc ///
Key
 castelnuovoSurface
 (castelnuovoSurface, PolynomialRing)
Headline
 construct the castelnuovo surface
Usage
 X= castelnuovoSurface P4
Inputs
 P4:PolynomialRing
  coordinate ring of P4
Outputs
 X:Ideal
  of the del Pezzo in P4
Description
  Text
    We construct a Castelnuovo surface from its Hilbert-Burch matrix
  Example
    kk=ZZ/nextPrime 10^3;
    P4=kk[x_0..x_4];
    minimalBetti(X=castelnuovoSurface P4)
    (d,sg)=(degree X, sectionalGenus X)
    Ksquare(5,2,1)
  Text
    X is a conic bundle. We compute the number of singular fibers.
  Example
    P1=kk[z_0,z_1]
    P4xP1=P4**P1
    fibration=ideal(sub(syz gens X,P4xP1) * transpose sub(vars P1,P4xP1));
    singFibration= fibration+minors(3,diff(transpose sub(vars P4,P4xP1), gens fibration));
    singularFibers=trim sub(saturate(singFibration,ideal sub(vars P4,P4xP1)),P1)
    degree singularFibers
  Text
    The are 7 singular fibers,
    which fits with Ksquare=1==8-7
///

doc ///
Key
 degree8OkonekSurface
 (degree8OkonekSurface, PolynomialRing, Ring)
Headline
 construct a degree 8 Okonek surface
Usage
 X= degree8OkonekSurface P4
Inputs
 P4:PolynomialRing
  coordinate ring of P4
Outputs
 X:Ideal
  of the cubic scroll in P4
Description
  Text
    We construct the surface from a randomly choosen differential T.dd_3
    of the Tate resolution of the desired ideal.
  Example
    kk=ZZ/nextPrime 10^3;
    P4=kk[x_0..x_4];
    E=kk[e_0..e_4,SkewCommutative=>true];
    minimalBetti(X=degree8OkonekSurface(P4,E))
    degree X, sectionalGenus X
    betti(T=tateResolutionOfSurface X)
    betti T.dd_3
///

doc ///
Key
 ionescuOkonekSurface
 (ionescuOkonekSurface, PolynomialRing,PolynomialRing)
Headline
 construct a Ionescu-Okonek surface
Usage
 X= ionescuOkonekSurface(P4,P2)
Inputs
 P4:PolynomialRing
  coordinate ring of P4
 P2:PolynomialRing
  coordinate ring of P2
Outputs
 X:Ideal
  of a Ionescu-Okonek surface in P4
Description
  Text
    We construct a Ionescu-Okonek surface from its rational parametrization.
  Example
    kk=ZZ/nextPrime 10^3;
    P4=kk[x_0..x_4];
    P2=kk[y_0..y_2];
    minimalBetti(X=ionescuOkonekSurface(P4,P2))
    degree X, sectionalGenus X
///

doc ///
Key
 degree10DESSurface
 (degree10DESSurface,PolynomialRing,Ring)
Headline
 construct the degree 10 Decker-Ein-Schreyer surface
Usage
 X=degree10DESSurface(P4,E)
Inputs
 P4:PolynomialRing
  coordinate ring of P4
 E:Ring
  dual exterior algebra
Outputs
 X:Ideal
  of a degree 10 Decker-Ein-Schreyer surface in P4
Description
  Text
    We construct the surface from a randomly choosen differential T.dd_4
    of the Tate resolution of the desired ideal.
  Example
    kk=ZZ/nextPrime 10^3;
    P4=kk[x_0..x_4];
    E=kk[e_0..e_4,SkewCommutative=>true];
    minimalBetti(X=degree10DESSurface(P4,E))
    degree X, sectionalGenus X
    betti(T=tateResolutionOfSurface X)
    betti(T.dd_4)
///

doc ///
Key
 degree10pi8RanestadSurface
 (degree10pi8RanestadSurface, PolynomialRing)
Headline
 construct a degree 10 sectional genus 8 Ranestad surface
Usage
 X= degree10pi8RanestadSurface P4
Inputs
 P4:PolynomialRing
  coordinate ring of P4
Outputs
 X:Ideal
  of a degree 10 sectional genus 8 Ranestad surface in P4
Description
  Text
    We construct the surface from a carefully choosen H^1_*(I_X) module of the ideal sheaf I_X
    with Hilbert function (2,5,3).
  Example
    kk=ZZ/nextPrime 10^3;
    P4=kk[x_0..x_4];
    minimalBetti(X=degree10pi8RanestadSurface P4)
    betti(T=tateResolutionOfSurface X)
    (d,sg)=(degree X, sectionalGenus X)
    LeBarzN6(d,sg,1)==6
    Ksquare(d,sg,1)==-4

SeeAlso
   enriquesSurfaceOfDegree10
   adjunctionProcessData
///


doc ///
Key
 enriquesSurfaceOfDegree10
 (enriquesSurfaceOfDegree10, PolynomialRing)
Headline
 construct an Enriques surface of degree 10 
Usage
 X= enriquesSurfaceOfDegree10 P4
Inputs
 P4:PolynomialRing
  coordinate ring of P4
Outputs
 X:Ideal
  of an Enriques surface of degree 10 in P4
Description
  Text
    We construct the surface from a carefully choosen H^1_*(I_X) module of the ideal sheaf I_X
    with Hilbert function (2,5,3).
  Example
    kk=ZZ/nextPrime 10^3;
    P4=kk[x_0..x_4];
    minimalBetti(X=enriquesSurfaceOfDegree10 P4)
    betti(T=tateResolutionOfSurface X)
    (d,sg)=(degree X, sectionalGenus X)
    LeBarzN6(d,sg,1)==6
    Ksquare(d,sg,1)==-4
    X5=ideal (gens X)_{0..9};
    R=X5:X;
    dim R,degree R
    elapsedTime (numList,L1,L2,Y)=adjunctionProcess(X,1);
    numList
    minimalBetti Y
    2*sectionalGenus Y- 2== degree Y
    fourPoints=saturate L2_0;
    dim fourPoints,degree fourPoints
  Text
    The first adjunction maps blows down 4 (-1) lines. Hence the self-intersection number of the
    canonical divisor on Y is K_Y^2=K_X^2+4=0. Moreover H_Y.K_Y=0. So K_Y is numerically
    trivial and Y is a minimal Enriques surface.
    
SeeAlso
    degree10pi8RanestadSurface
    adjunctionProcessData
///


doc ///
Key
 degree10pi9RanestadSurface
 (degree10pi9RanestadSurface, PolynomialRing,Ring)
Headline
 construct a degree 10 sectional genus 9 Ranestad surface
Usage
 X= degree10pi8RanestadSurface(P4,E)
Inputs
 P4:PolynomialRing
  coordinate ring of P4
 E:Ring
   dual exterior algebra
Outputs
 X:Ideal
  of a degree 10 sectional genus 9 Ranestad surface in P4
Description
  Text
    We construct the surface from a carefully choosen differential T.dd_4
    of the Tate resolution.
  Example
    kk=ZZ/nextPrime 10^3;
    P4=kk[x_0..x_4];
    E=kk[e_0..e_4,SkewCommutative=>true];
    minimalBetti(X=degree10pi9RanestadSurface(P4,E))
    betti(T=tateResolutionOfSurface X)
    betti(T.dd_4)
    degree X, sectionalGenus X
///

doc ///
Key
 nonspecialAlexanderSurface
 (nonspecialAlexanderSurface, PolynomialRing)
 (nonspecialAlexanderSurface, PolynomialRing,PolynomialRing)
Headline
 construct a nonspecial Alexander surface of degree 9
Usage
 X= nonspecialAlexanderSurface P4
 X= nonspecialAlexanderSurface(P4,P2)
Inputs
 P4:PolynomialRing
  coordinate ring of P4
 P2:PolynomialRing
  coordinate ring of P2 
Outputs
 X:Ideal
  of a nonspecial Alexander surface of degree 9 in P4
Description
  Text
    We construct a nonspecial Alexander surface of degree 9 from its rational parametrization,
    or what is faster from a presentation of the H^1_*(I_X) module. The dual of the (3,5,1) module has
    a special presentation which gives rize to a six secant line
  Example
    kk=ZZ/nextPrime 10^3;
    P4=kk[x_0..x_4];
    elapsedTime minimalBetti(X=nonspecialAlexanderSurface(P4))
    X5=ideal (gens X)_{0..14};
    L=X5:X -- L is the six secant line
    degree(L+X)==6
    P2=kk[y_0..y_2];
    elapsedTime minimalBetti(X=nonspecialAlexanderSurface(P4,P2))
    degree X, sectionalGenus X
    betti(T=tateResolutionOfSurface X)
    X5=ideal (gens X)_{0..14};
    L=X5:X -- L is the six secant line
    degree(L+X)==6

SeeAlso
   enriquesSurfaceOfDegree9
///

doc ///
Key
 enriquesSurfaceOfDegree9
 (enriquesSurfaceOfDegree9, PolynomialRing)
 
Headline
 construct a Enriques surface  of degree 9
Usage
 X=  enriquesSurfaceOfDegree9 P4
Inputs
 P4:PolynomialRing
  coordinate ring of P4
Outputs
 X:Ideal
  of an Enriques surface of degree 9 in P4
Description
  Text
    We construct the Enriques surface from a presentation of the H^1_*(I_X) module. The dual of the (3,5,1) module
    is defined by 12 quadrics and completely determines X. In the dual projective space P4^*
    this corresponds to a canonical curve of genus 5 defined by 3=15-12 quadrics.
    The Enriques surface is non-minimal. It is the projection of a Fano polarized minimal
    Enriques surface in P5. Thus the universal family of the Hilbert scheme of Fano polarized
    Enriques surfaces is birational to the Hilbert scheme of canonical curves of genus 5 in P5.
  Example
    kk=ZZ/nextPrime 10^3;
    P4=kk[x_0..x_4];
    elapsedTime minimalBetti(X=enriquesSurfaceOfDegree9(P4))
    betti(T=tateResolutionOfSurface X)
    (d,sg)=(degree X, sectionalGenus X)
    Ksquare(d,sg,1)==-1
    LeBarzN6(d,sg,1)
    elapsedTime (numList,L1,L2,Y)=adjunctionProcess(X,1);
    numList
    minimalBetti Y
    2*sectionalGenus Y -2== degree Y
    point=saturate L2_0
    dim point
  Text
    The self-intersection number of the canonical divisor on the first adjoint surface Y
    is K_Y^2=K_X^2+1=0. Moreover H_Y.K_Y =0. Hence K_Y is numerically trivial
    and Y is a minimal Enriques surface. 
SeeAlso
   nonspecialAlexanderSurface
   adjunctionProcessData
///






doc ///
Key
 specialityOneAlexanderSurface
 (specialityOneAlexanderSurface, PolynomialRing,Ring)
Headline
 construct a speciality One AlexanderSurface Alexander surface of degree 9
Usage
 X= specialityOneAlexanderSurface(P4,E)
Inputs
 P4:PolynomialRing
  coordinate ring of P4
 P2:PolynomialRing
  coordinate ring of P2 
Outputs
 X:Ideal
  of a speciality one Alexander surface of degree 9 in P4
Description
  Text
    We construct a speciality 1 Alexander Surfac of degree 9 from its differential
    T.dd_4 of the Tate resolution.
  Example
    kk=ZZ/nextPrime 10^3;
    P4=kk[x_0..x_4];
    E=kk[e_0..e_4,SkewCommutative=>true];
    elapsedTime minimalBetti(X=specialityOneAlexanderSurface(P4,E))
    degree X, sectionalGenus X
    betti(T=tateResolutionOfSurface X)
    betti(T.dd_4)
    betti res(coker random(target T.dd_4,source T.dd_4),LengthLimit=>4)
    betti res(coker transpose random(target T.dd_4,source T.dd_4),LengthLimit=>5)
  Text
    Thus a random choice of the differential T.dd_4 leads to a surface and the component of the Hilbert scheme is unirational
    
///

doc ///
Key
 popescuSurface
 (popescuSurface, PolynomialRing,Ring,Number)
Headline
 construct a Popescu surface 
Usage
 X= popescuSurface(P4,E,s)
Inputs
 P4:PolynomialRing
  coordinate ring of P4
 E:Ring
  dual exterior algebra
 s: Number
  the number of desired 6-secants
Outputs
 X:Ideal
  of a Popescu surface in P4
Description
  Text
   The Popescu surfaces come in three families, distinguished by their
   number of 6-secant lines.
   One has to choose the differential T.dd_4 suitable.
   In the first case X has no 6-secant, since the ideal is generated by quintics. 
  Example
   kk=ZZ/nextPrime 10^3;
   P4=kk[x_0..x_4];
   E=kk[e_0..e_4,SkewCommutative=>true];
   minimalBetti(X=popescuSurface(P4,E,0))
   (d,sg)=(degree X, sectionalGenus X) 
   betti(T=tateResolutionOfSurface X)
  Text
   In the second case there is a unique 6-secant line.
  Example
   elapsedTime minimalBetti(X=popescuSurface(P4,E,1))
   X5=ideal (gens X)_{0..9};
   L=X5:X, degree(L+X)
   elapsedTime (numList,L1,L2,J)=adjunctionProcess(X,1);
   numList_1
  Text
   The entry numList_1 is the number of (-1) lines on X. Thus we must have
  Example
   LeBarzN6(d,sg,1)==6+1
  Text
   In the third case there is a pencil of 6-secant line. Every line in
   the plane through the point is a 6-secant line,
   since the plane intersects the surface in a plane quintic curve.
  Example
   elapsedTime minimalBetti(X=popescuSurface(P4,E,2))
   X5=ideal (gens X)_{0..9};
   R=X5:X 
   tally apply(primaryDecomposition (R+X),c->(dim c,degree radical c,degree(c+R)))

    
SeeAlso
  adjunctionProcessData

///
 

doc ///
Key
 randomSurfaceDegreeAndSectionalGenus
 (randomSurfaceDegreeAndSectionalGenus, Function, List)
Headline
 construct of a random rational surface of a given type
Usage
 dsg = randomSurfaceDegreeAndSectionalGenus(F,ringList)
Inputs
 F:Function
     which produces a surface in P4
 ringList:List
    {P4,E,P2} of the coordinate ring of P4, the corresponding exterior algebra and the coordinate ring  of P2
Outputs
  dsg:List
    of the degree d and the sectional genus of the surface
Description
  Text
   The unirational components of the Hilbert scheme of smooth surfaces in P4 uses in the construction
   P4, or P4 and E ,or P4 and P2. This functions calls the corresponding function of the construction
   The function computes examples of the desired surface and prints
   some numerical information. It returns the degree and the sectional genus 
  Example
    kk=ZZ/nextPrime 10^3;
    P4=kk[x_0..x_4];    
    E=kk[e_0..e_4,SkewCommutative=>true];
    P2=kk[y_0..y_2];
    ringList={P4,E,P2};
    Fs={bordigaSurface,ionescuOkonekSurface,degree8OkonekSurface,nonspecialAlexanderSurface,specialityOneAlexanderSurface}
    elapsedTime dges=apply(Fs,F->randomSurfaceDegreeAndSectionalGenus(F,ringList))
    Fs1={degree10pi8RanestadSurface,degree10pi9RanestadSurface,degree10DESSurface};
    --apply(Fs1,F->elapsedTime randomSurfaceDegreeAndSectionalGenus(F,ringList))   
  Text
    The last command should not be executed since it takes too much time.

Caveat
   
SeeAlso
  
///

-* Test section *-
TEST///

///

end--

-* Development section *-

restart

uninstallPackage "NongeneralTypeSurfacesInP4"
restart
loadPackage ("NongeneralTypeSurfacesInP4",Reload=>true)
installPackage "NongeneralTypeSurfacesInP4"

viewHelp "NongeneralTypeSurfacesInP4"
check "NongeneralTypeSurfaceInP4"
path
viewHelp 
kk=ZZ/nextPrime 10^3; P4=kk[x_0..x_4]
aboRanestadWithLinearSyzygy=method(Options=>{Verbose=>false,Smooth=>true,Special=>0})
aboRanestadWithLinearSyzygy(Ring) := opt -> P4 -> (
    (E,m2x3,bs,as,B,ExB,E2,b4x2,a2x3,E3)=prepareAboRanestadSurfaces P4;
    kk=coefficientRing P4;
    count=1;test=0;countSmooth=1;
    while( --smooth
    while( -- dim X and degree X
    while( -- test1 and test2
	while(m3x3=random(kk^3,kk^3);det m3x3 ==0 ) do ();
	while( m2x2=random(kk^2,kk^2);det m2x2==0) do ();
	m2x3a=(m2x2*m2x3*m3x3);
	m1x3b=map(E^1,E^0,0);
	scan(3,i->(
	    while (rd=random(kk^1,kk^2);rd_(0,1)==0) do ( );
	    m1x3b=m1x3b|rd*(m2x3a_{i})
	));
        m2x4=m2x3a^{0}||m1x3b;
	while( m2x2=random(kk^2,kk^2);det m2x2==0) do ();
	m2x4=m2x4|(m2x2*m2x3*random(kk^3,kk^1));
        --m2x4=m2x4|random(E^2,E^{-1});
	m4x2=transpose m2x4;
	c=b4x2*sub(m2x3,ExB)+sub(m4x2,ExB)*a2x3;
	I=trim ideal sub(contract(E3,flatten c),B);
	if opt.Verbose then (<< "numgens I = " <<numgens I <<endl);
	sol=vars B%I;
	randSol=sub(sol,random(kk^1,kk^140));
	b4x2r=sub(b4x2,vars E|randSol);
	betti(bb=map(E^4,,m4x2|b4x2r));
	--betti syz bb, betti syz transpose bb
	test1 = degrees source syz bb =={{3}, {3}, {3}, {4}, {4}, {4}, {4}, {4}};
	test2 = degrees source syz transpose bb=={{2}, {2}, {2}, {2}, {2}, {2}, {2}, {2}, {2}, {2}, {2}, {2}, {2}};
        not(test1 and test2)
	) do (test=test+1;count=count+1);
    if opt.Verbose then (<<"trials so far to get a surface = " <<count <<endl);
    betti(T=res(coker bb, LengthLimit=>4));
    X=saturate ideal syz symExt(T.dd_4,P4);
    not (dim X ==3 and degree X==12) ) do ();
    if not opt.Smooth then return (X,m4x2);
    singX=X+minors(2,jacobian X);
    dim singX !=0) do (countSmooth=countSmooth+1);
    if opt.Verbose then (<<"trials to get a smooth surface = "<<countSmooth <<endl);
    (X,m4x2))

///
elapsedTime (X,m4x2)=aboRanestadWithLinearSyzygy(P4,Verbose=>true,Smooth=>true);
minimalBetti X
curve=minors(2,sub(m4x2,vars P4));
scroll = minors(2,sub(m2x3,vars P4))
pt=saturate(curve+scroll)
(pts,vP2,vP3,g25)=veroneseImagesInG25(m4x2);
dim pts, degree pts

kk=ZZ/101
P4=kk[x_0..x_4]
scroll = minors(2,matrix{{P4_0,P4_1,P4_3},{P4_1,P4_2,P4_4}})
elapsedTime L=apply(4,i->(
	elapsedTime (X,m4x2)=aboRanestadWithLinearSyzygy(P4,Verbose=>true,Smooth=>true);
	curve=minors(2,sub(m4x2,vars P4));
	--<<(dim curve, degree curve) <<endl;
	pt=saturate(curve+scroll);
	<<betti pt<<endl;
	(pts,vP2,vP3,g25)=veroneseImagesInG25(m4x2);
	elapsedTime (L0,L1,L2,J)=adjunctionProcess(X,1);
	<<"number of exceptional lines = " <<L0_1 <<endl;
	<<(minimalBetti X, L0_1, (dim pts,degree pts), (dim pt, degree pt))<<endl;
	(X,m4x2)));


kk=ZZ/19
P4=kk[x_0..x_4]
scroll = minors(2,matrix{{P4_0,P4_1,P4_3},{P4_1,P4_2,P4_4}})
elapsedTime LL0=apply(toList(4..8),i->tally apply(4,j->(
	elapsedTime (X,m4x2)=aboRanestadSurface(P4,i,Verbose=>true,Smooth=>true);
	curve=minors(2,sub(m4x2,vars P4));
	--<<(dim curve, degree curve) <<endl;
	pt=saturate(curve+scroll);
	<<(dim pt,degree pt)<<endl; 
	(pts,vP2,vP3,g25)=veroneseImagesInG25(m4x2);
	elapsedTime (L0,L1,L2,J)=adjunctionProcess(X,3);
	<<minimalBetti J<<endl;
	<<"number of exceptional lines = " <<L0_1 <<endl;
	<<(minimalBetti X, L0_1, (dim pts,degree pts), (dim pt, degree pt))<<endl;
	(i,L0, (dim pts,degree pts), (dim pt, degree pt))
	)))
tally LL0
-*
o12 = Tally{(4, {(4, 12, 13), 4, (12, 24, 13), 12, (12, 16, 5), 0, (4, 4, 1)}, (1, 3), (-1, 0)) => 1}
            (5, {(4, 12, 13), 5, (12, 24, 13), 9, (12, 17, 6), 3, (5, 5, 1)}, (1, 4), (-1, 0)) => 1
            (6, {(4, 12, 13), 6, (12, 24, 13), 6, (12, 18, 7), 6, (6, 6, 1)}, (1, 5), (1, 2)) => 1
            (7, {(4, 12, 13), 7, (12, 24, 13), 4, (12, 19, 8), 5, (7, 8, 2)}, (1, 6), (1, 2)) => 1
            (8, {(4, 12, 13), 8, (12, 24, 13), 1, (12, 20, 9), 8, (8, 9, 2)}, (1, 7), (1, 2)) => 1

*-
elapsedTime LL2=apply(toList(6..8),i->(
	elapsedTime (X,m4x2)=aboRanestadSurface(P4,i,Special=>2,Verbose=>true,Smooth=>true);
	curve=minors(2,sub(m4x2,vars P4));
	--<<(dim curve, degree curve) <<endl;
	pt=saturate(curve+scroll);
	<<(dim pt,degree pt)<<endl; 
	(pts,vP2,vP3,g25)=veroneseImagesInG25(m4x2);
	elapsedTime (L0,L1,L2,J)=adjunctionProcess(X,3);
	<<"number of exceptional lines = " <<L0_1 <<endl;
	<<(minimalBetti X, L0_1, (dim pts,degree pts), (dim pt, degree pt))<<endl;
	(i,L0, (dim pts,degree pts), (dim pt, degree pt))
	))
tally LL2

restart
loadPackage ("NongeneralTypeSurfacesInP4",Reload=>true)
kk=ZZ/19
P4=kk[x_0..x_4]
scroll = minors(2,matrix{{P4_0,P4_1,P4_3},{P4_1,P4_2,P4_4}})
elapsedTime LL8=apply(6,i->(
	elapsedTime (X,m4x2)=aboRanestadSurface(P4,8,Verbose=>true,Smooth=>true);
	<<minimalBetti X<<endl;
	curve=minors(2,sub(m4x2,vars P4));
	--<<(dim curve, degree curve) <<endl;
	pt=saturate(curve+scroll);
	<<(dim pt,degree pt,betti pt,pt)<<endl; 
	(pts,vP2,vP3,g25)=veroneseImagesInG25(m4x2);
	elapsedTime (L0,L1,L2,J)=adjunctionProcess(X,3);
	<< minimalBetti J<<endl;
	<<"number of exceptional lines = " <<L0_1 <<endl;
	<<(L0_1, (dim pts,degree pts), (dim pt, degree pt))<<endl;
	(minimalBetti X ,L0, (dim pts,degree pts), (dim pt, degree pt))
	));
tally LL8

restart
loadPackage ("NongeneralTypeSurfacesInP4",Reload=>true)
kk=ZZ/19
P4=kk[x_0..x_4]
scroll = minors(2,matrix{{P4_0,P4_1,P4_3},{P4_1,P4_2,P4_4}})
elapsedTime LL7=apply(4,i->(
	elapsedTime (X,m4x2)=aboRanestadSurface(P4,7,Verbose=>true,Smooth=>true);
	<<minimalBetti X<<endl;
	curve=minors(2,sub(m4x2,vars P4));
	--<<(dim curve, degree curve) <<endl;
	pt=saturate(curve+scroll);
	<<(dim pt,degree pt,betti pt,pt)<<endl; 
	(pts,vP2,vP3,g25)=veroneseImagesInG25(m4x2);
	elapsedTime (L0,L1,L2,J)=adjunctionProcess(X,3);
	<< minimalBetti J <<endl;
	<<"number of exceptional lines = " <<L0_1 <<endl;
	<<(L0_1, (dim pts,degree pts), (dim pt, degree pt))<<endl;
	(minimalBetti X ,L0, (dim pts,degree pts), (dim pt, degree pt))
	));
tally LL7




scroll = minors(2,matrix{{P4_0,P4_1,P4_3},{P4_1,P4_2,P4_4}})
elapsedTime L=apply(2,i->(
	elapsedTime (X,m4x2)=aboRanestadSurface(P4,4,Verbose=>true,Smooth=>true);
	curve=minors(2,sub(m4x2,vars P4));
	--<<(dim curve, degree curve) <<endl;
	pt=saturate(curve+scroll);
	<<betti pt<<endl; <<pt <<endl;
	(pts,vP2,vP3,g25)=veroneseImagesInG25(m4x2);
	elapsedTime (L0,L1,L2,J)=adjunctionProcess(X,1);
	<<"number of exceptional lines = " <<L0_1 <<endl;
	<<(minimalBetti X, L0_1, (dim pts,degree pts), (dim pt, degree pt))<<endl;
	(X,m4x2)));


pt=saturate(curve+scroll)
dim pt, degree pt
minimalBetti scroll, minimalBetti curve
///


doc ///
Key
 schreyerSurfaceWith2LinearSyzygies
 (schreyerSurfaceWith2LinearSyzygies, Ring)
Headline
 compute a rational Schreyer surface whose H^1-module has 4 extra syzyzgies
Usage
 X = schreyerSurfaceWith2LinearSyzygies P4
Inputs
 P4:Ring
  the coordinate ring of P4
Outputs
 X:Ideal
  the ideal of a smooth Schreyer surface
Description
  Text
    The construction is a 2 step liaison construction.
    The desired surface has a residual scheme R=X5:X consisting on union of 3 planes.
    A general (5,5) complete intersection ci has as residual scheme ci:X=R cup Y with
    Y a surface of degree 11 which lies on two quartics. The (4,4) complete intersection
    ci2 has residual Z=ci2:Y of degree 5 which decomposes in a cubic scroll and a quadric surface
    which intersect along the directrix of the scroll and two non-CM points of Z.
  Example
    kk=ZZ/nextPrime 10^3;
    P4=kk[x_0..x_4];
    elapsedTime X=schreyerSurfaceWith2LinearSyzygies(P4);
    minimalBetti X
    M=moduleFromSchreyerSurface X;
    minimalBetti M
    X5=ideal (gens X)_{0..4};
    R=X5:X;
    minimalBetti radical R
    apply(decompose R,c->(dim c, degree c, minimalBetti c))
    ci=ideal( gens X*random(source gens X,P4^{2:-5}));
    Y=(ci:X):R;
    degree Y,betti(fY=res Y)
    nCM=decompose ann coker transpose fY.dd_3
    ci2=ideal (gens Y)_{0,1};
    Z=ci2:Y;
    minimalBetti Z
    cZ=decompose Z;
    tally apply(cZ,c->(dim c, degree c, minimalBetti c))
  Text
    The construction is a reversal of this linkage. Note that both Y and Z are not Cohen-Macaulay
    in two (common) points.     
  Example    
    intersectionOftheTwoComponentsOfZ=sum(cZ);
    apply(cI=decompose intersectionOftheTwoComponentsOfZ,c->(dim c, degree c))
    cI, cI_{1,2}==nCM
    planes=decompose R
    matrix apply(planes,p2->apply(nCM,p->dim(p2+p)))
    matrix apply(planes,p2->apply(planes,p2'->dim(p2+p2')))
    dim(radical R+Z),degree(radical R+Z)
    matrix apply(planes,p2->apply(cZ,c->degree(p2+c)))
    m3x2=(res cZ_1).dd_2
    syz transpose (m3x2%cI_0) -- => cI_0 is the directrix of the scroll
///


kk=ZZ/2
P4=kk[x_0..x_4]
P2=kk[t_0..t_2]
X=vBELSurface(P4,P2);
minimalBetti X
X5=ideal(gens X)_{0..5};
R=X5:X;
dim R, degree R, minimalBetti R
ci=ideal(gens X*random(source gens X,P4^{-4,-5}));
minimalBetti (Y=ci:X)
degree Y, genera Y
singY=saturate(Y+minors(2,jacobian Y));
decompose singY
cY=decompose Y
tally apply(cY,c->(dim c, degree c, minimalBetti c))
matrix apply(cY,c->apply(cY,d->degree(c+d)))
matrix apply(cY,c->apply(decompose R,d->dim(c+d)))
