///
restart
needsPackage"NongeneralTypeSurfacesInP4"

installPackage "NongeneralTypeSurfacesInP4"

uninstallPackage "NongeneralTypeSurfacesInP4"
restart
loadPackage ("NongeneralTypeSurfacesInP4")--,Reload=>true)
installPackage("NongeneralTypeSurfacesInP4")--,MakePDF=>true)

viewHelp "NongeneralTypeSurfacesInP4"
check "NongeneralTypeSurfaceInP4"
path
peek loadedFiles
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
    PackageExports => {"BGG","AdjunctionForSurfaces","PrimaryDecomposition"},
    Keywords => {"Algebraic Geometry"}
    )

export {
    --"NongeneralTypeSuracesInP4",
    "sectionalGenus",
    "chiI",
    "chiITable",
    "HdotK",
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
    "enriquesSurfaceD11S10",
    "k3Surfaces",
    "horrocksMumfordSurface",
    "ellipticSurface",
    "unirationalFamilies",
    "constructionsViaFiniteFieldSearches",
    "extensionToCharacteristicZero",
    "LabBookProtocol",
    "knownExamples",
    "unirationalFamiliesOfRationalSurfaces",
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
    "vBELSurface",
    "quinticEllipticScroll",
    "ellipticConicBundle",
    "irregularEllipticSurfaceD12",
    "regularEllipticSurfaceD12",
    "biellipticSurfaceD10",
    "biellipticSurfaceD15",
    "abelianSurfaceD10",
    "abelianSurfaceD15",
    "abelianSurfaceD15S21Popescu",
    "K3surfaceD7",
    "K3surfaceD8",
    "K3surfaceD9",
    "K3surfaceD10S9SL1",
    "K3surfaceD10S9SL3",
    "H1module",
    "K3surfaceD11S11SLn",
    "K3surfaceD11S12",
    "K3surfaceD12",
    "K3surfaceD13",
    "K3surfaceD14",
    "ellipticSurfaceD7",
    "ellipticSurfaceD8",
    "ellipticSurfaceD9",
    "ellipticSurfaceD10S9",
    "ellipticSurfaceD10S10",
    "ellipticSurfaceD12S14L0",
    "ellipticSurfaceD12S14Linfinite",
    "K3surfaces",
    "surfacesOfKodairaDimension1",
}


-* Code section *-
-* numerical functions *-
sectionalGenus=method()
sectionalGenus(Ideal):= X -> (genera X)_1

chiI=method()
chiI(Number,Number,Number) := (m,d,sg) -> binomial(m+4,4)-(binomial(m+1,2)*d-m*(sg-1)+1)



chiITable=method()
chiITable(Number,Number) := (d,sg) -> apply(toList(-1..5),m->chiI(m,d,sg))

HdotK=method()
HdotK(Number,Number) := (d,sg) -> 2*(sg-1)-d
   
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
vBELSurface(Ring,Ring) := (P4,P2) -> ( -- the specific surface from the vBEL paper
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


vBELSurface(PolynomialRing) := P4 -> (
    kk:= coefficientRing P4;
    u := symbol u;
    P2:=kk[u_0..u_2];
    p123:=ideal(u_0*u_1,u_0*u_2,u_1*u_2);
    p5:=minors(2,random(P2^2,P2^{2:-1,-2}));-- five general points
    p8:=saturate intersect(p123^2,p5);-- double points at p123, simple at p5
-- betti p8-- a unique quartic (gens p8)_{0} in p8
   p122:=ideal(u_1+u_2)+ideal (gens p8)_{0};
   p2:=p122:p123^2;-- two points in line through (1:0:0)
   p10:=saturate(intersect(p2,p123,p5)); --ideal of 10 points (for Bordiga)
   assert(betti res p10==new BettiTally from {(0,{0},0) => 1, (1,{4},4) => 5, (2,{5},5) => 4});
   xx:= ideal gens P4;
   F:=map(P2,P4,gens p10);
   s6:=kernel F;--Bordiga surface
   s60:=preimage (F,ideal(u_1+u_2));--a (-2)-line in s6
   s622:=preimage (F,ideal (gens p8)_{0});--a twisted cubic curve in s6
   s6h:=ideal(gens s622)_{0}+s6;--the hyperplane section of s6 containing s622
   s612:=s6h:s622;--three (-1)-lines residual to s622 in s6h
   s61200:=saturate(s60+s612);--the point of intersection between s60 and a line in s612
   --betti s61200
   s620x:=preimage (F,ideal (u_1^2,u_2*u_1,u_2^2));
   s6201:=ideal (gens s620x)_{0..2};--the (-1)-line in s6 over (1:0:0) 
   --betti s620x
   ts61200:=gens xx* gens kernel(diff(gens xx,transpose gens s61200));
   ts62h:=ideal(gens s612)_{0..1}+ideal flatten diff( ts61200, (gens s612)_{1});
   s601:=ts62h:s6201;-- the line in s6 through s61200, different from s6201
--betti s601
--degree(s601+s612)--the line s601 intersect all three lines in s612
   s602:=saturate intersect(s60,s601);--the union of the lines s60 and s601
--betti s602
   s1:=ideal(gens s602)_{0..1}; --the plane spanned by the lines s60 and s601
   s2:=ideal(gens s612)_{0..1};-- the quadric surface containing the three lines in s612
   s9:=saturate intersect (s1,s2,s6);--a surface of degree 9
   assert(minimalBetti s9== new BettiTally from {(0,{0},0) => 1, (1,{4},4) => 1, (1,{5},5) => 12, (2,{6},6) => 23, (3,{7},7) => 14, (4,{8},8) => 3}); -- proceed if it is contained in one quartic
   s20:=ideal (gens s9 * random(source gens s9, P4^{-4,-5}));
   X:=s20:s9;-- A surface of degree 11, genus 11
   assert( (dim X, degree X, (genera X)_1)==(3,11,11));
   X)
///
kk=ZZ/nextPrime 10^3
P4=kk[x_0..x_4]
X= vBELSurface P4;
minimalBetti X
singX=saturate(X+minors(2,jacobian X))
dim singX==-1


r45=ideal (gens X)_{0..5};
Rest=r45:X;
degree Rest, dim Rest, genus Rest--two lines
degree (Rest+X), dim (Rest+X)-- 6-secants
degree (Rest+s2), dim (Rest+s2)-- lie in the quadric surface s2.
///

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

enriquesSurfaceD11S10 = method()
enriquesSurfaceD11S10(PolynomialRing) := P4 -> (
    if char P4 != 3 then error "Need a ground field of characteristic 3";
    X:=specificSchreyerSurface(P4,0)
    )

///
kk=ZZ/3
P4=kk[x_0..x_4]
minimalBetti (X=enriquesSurfaceD11S10(P4))
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

-* from Hiro *-


quinticEllipticScroll=method()
-- Quintic elliptic scroll (B2.1)
--     PURPOSE : Construct an quintic elliptic scroll, which is a nonsingular surface of degree 5 and sectional genus 1
--       INPUT : 'P4', the homogeneous coordinate ring of projective fourspace 
--      OUTPUT : Ideal of the quintic elliptic scroll
-- DESCRIPTION : This function constructs an quintic elliptic surface as the degeneracy locus of a map between two vector bundles

quinticEllipticScroll(PolynomialRing):=P4 -> (
    -- Compute the koszul complex of the variables of 'P4'
    kos:=res coker vars P4;
    -- Construct a variety 'X' as the degenerate locus of the map from 5O(-3) to the second Koszul syzygy module 
    X:=trim ideal syz transpose (kos.dd_4 | random(source kos.dd_3,P4^{5:-3}));
    -- Check whether 'X' is a surface with the desired degree and sectional genus 
    assert(dim X==3 and degree X==5 and sectionalGenus X==1);
    X)

ellipticConicBundle=method()
-- Elliptic conic bundle which was missing in Okonek's paper
--     PURPOSE : Construct an elliptic conic bundle, which is a nonsingular surface of degree 8 and sectional genus 5
--       INPUT : 'P4', the homogeneous coordinate ring of projective fourspace 
--      OUTPUT : Ideal of the elliptic conic bundle
-- DESCRIPTION : This function constructs an quintic elliptic surface as the degeneracy locus of a map between two vector bundles

ellipticConicBundle(PolynomialRing) := P4 -> (
    -- Compute a koszul complex3
    kos:=res coker matrix{{P4_0..P4_2,P4_3,P4_4^2}};
    -- Define a map from the second Koszul syzygy module to O(-1) 
    f:=map(P4^{1:-1},target kos.dd_3,{{1,3:0,2:1,4:0}})*kos.dd_3;
    -- Construct the kernel of 'f'
    K:=prune homology(f,kos.dd_4);
    -- Define a variety 'X' as the degenerate locus of the map from 4O(-4) to 'K'
    X:=trim ideal syz transpose (presentation K | random(source gens K,P4^{4:-4}));
    -- Check whether 'X' is a surface with the desired degree and sectional genus 
    assert(dim X==3 and degree X==8 and sectionalGenus X==5);
    X)


irregularEllipticSurfaceD12=method()
-- Irregular elliptic surface of degree 12 and sectional genus 13 obtained as the dependency locus of two global sections of a rank three vector bundle
--     PURPOSE : Construct a nonsingular irregular elliptic surface of degree 12 and sectional genus 13
--       INPUT : 'P4', the homogeneous coordinate ring of projective fourspace 
--      OUTPUT : Ideal of the elliptic surface
-- DESCRIPTION : This function constructs an irregular elliptic surface as the degeneracy locus of a map between two vector bundles

irregularEllipticSurfaceD12(PolynomialRing) := P4 -> (
    -- Compute a koszul complex
    kos:=res coker matrix{{P4_0..P4_2,P4_3^2,P4_4^2}};
    -- Define a map from the second Koszul syzygy module to O(-1) 
    f:=map(P4^{1:-1},target kos.dd_3,{{1,4:0,-P4_0,2:0,P4_1,0}})*kos.dd_3;
     -- Construct the kernel of 'f'
    K:=prune homology(f,kos.dd_4);
    -- Define a variety 'X' as the degenerate locus of the map from O(-4)++3O(-5) to 'K'
    X:=trim ideal syz(transpose (presentation K | random(source gens K,P4^{1:-4,3:-5})),DegreeLimit=>0);
    -- Check whether 'X' is a surface with the desired degree and sectional genus 
    assert(dim X==3 and degree X==12 and sectionalGenus X==13);
    X)

regularEllipticSurfaceD12=method()
-- Regular elliptic surface of degree 12 and sectional genus 13 obtained as the dependency locus of two global sections of an extension of the HM bundle (B7.7)
--     PURPOSE : Construct a nonsingular regular elliptic surface of degree 12 and sectional genus 13
--       INPUT : 'P4', the homogeneous coordinate ring of projective fourspace 
--      OUTPUT : Ideal of the elliptic surface
-- DESCRIPTION : This function constructs a regular elliptic surface as the dependency locus of two sections of a rank three vector bundle
--     COMMENT : This function uses the BGG package

regularEllipticSurfaceD12(PolynomialRing) := P4 -> (
    KK:=coefficientRing P4;
    e:=symbol e; 
    -- Define an exterior algebra
    E:=KK[e_0..e_4,SkewCommutative=>true];
    -- Define morphisms 'alpha' and 'beta' of modules over 'E'
    beta:=map(E^{5:0},E^{2:-2},{{e_4*e_1,e_2*e_3},{e_0*e_2,e_3*e_4},{e_1*e_3,e_4*e_0},{e_2*e_4,e_0*e_1},{e_3*e_0,e_1*e_2}});
    alpha:=syz beta;
    beta=random(E^{4:0},target beta)*beta;
    -- Construct a Beilison monad; we use the command 'beilinson' to return the associated maps between direct sums of exterior powers of cotangent bundles
    alpha=beilinson(alpha,P4);
    beta=beilinson(beta,P4);
    -- Compute the homology of the monad, which is a rank three vector bundle (this vector bundle is an extension of the HM bundle by a line bundle) 
    K:=prune homology(beta,alpha);
    -- Define a variety 'X' as the dependency locus of two global sections of 'K'
    X:=trim ideal syz(transpose (presentation K | random(source gens K,P4^{2:-2})),DegreeLimit=>3);
    -- Check whether 'X' is a surface with the desired degree and sectional genus
    assert(dim X==3 and degree X==12 and sectionalGenus X==13);
    X)



biellipticSurfaceD10=method()
-- Bielliptic surface of degree 10 (B5.1)
--     PURPOSE : Construct a bielliptic surface, which is a nonsingular surface of degree 10 and sectional genus 6
--       INPUT : 'P4', the homogeneous coordinate ring of projective fourspace over the finite field of characteristic p
--      OUTPUT : Ideal of the bielliptic surface or 'null' if the function failed to find a surface
-- DESCRIPTION : This function first forms the Moore matrix, uses it to define a finite module, and a bielliptic surface as the degeneracy locus of a map from a vector bundle to the sheafified first syzygy module
--     COMMENT : The function could fail to find a surface, and if it fails, it return 'null' (this happens especually if 'p' is small) However, the function seems to find a surface when 'p' is large 

biellipticSurfaceD10(PolynomialRing):=P4->(
    z:=symbol z;
    S:=P4[z_0..z_4];
    -- Form the Moore matrix 'M'
    M:=matrix table(5,5,(i,j)->P4_((quotientRemainder(3*i+3*j,5))#1)*z_((quotientRemainder(3*i-3*j,5))#1));
    -- 'p' denotes the characteristic of 'P4'
    p:=char (coefficientRing P4);
    -- Define the eigenspace 'Pmin' corresponding to the eigenvalue 1 of the involution
    Pmin:=ideal(P4_1-P4_4,P4_2-P4_3);
    -- Define the quadric cone described in [ADHPR, Proposition 4.13] 
    Q:=ideal (P4_0^2+(P4_1+P4_4)*(P4_2+P4_3));
    -- Define the octic hypersurface described in [ADHPR, Proposition 4.19 (iii)] 
    --  Q':=ideal((P4_0*(P4_2*P4_4^2-P4_1^2*P4_3))^2+(P4_3*(P4_0*P4_2^2-P4_4^2*P4_1)+P4_2*(P4_4*P4_1^2-P4_3^2*P4_0))*(P4_1*(P4_3*P4_0^2-P4_2^2*P4_4)+P4_4(P4_1*P4_3^2-P4_0^2*P4_2)));
    Q':=ideal((P4_0*(P4_2*P4_4^2-P4_1^2*P4_3))^2+(P4_3*(P4_0*P4_2^2-P4_4^2*P4_1)+P4_2*(P4_4*P4_1^2-P4_3^2*P4_0))*(P4_1*(P4_3*P4_0^2-P4_2^2*P4_4)+P4_4*(P4_1*P4_3^2-P4_0^2*P4_2)));
    mu:=1;
    isGood:=false;
    -- Inside the following while loop, find an elliptic curve 'E' containing three ZZ/p-ratiinal nontrivial 2-torsion points and one F_p rational nontrivial 6-torsion point  
    while not isGood and mu<p do (
	E:=ideal for i from 0 to 4 list -mu*P4_((quotientRemainder(i,5))#1)^2-mu^2*P4_((quotientRemainder(i+1,5))#1)*P4_((quotientRemainder(i+4,5))#1)+P4_((quotientRemainder(i+2,5))#1)*P4_((quotientRemainder(i+3,5))#1);
	singE:=singularLocus E;
	c:=codim singE;
	if c!=5 then mu=mu+1;
	-- If E is nonsingular, take the intersection of 'E' with 'Pmin' to
	-- find nontrivial 2-torsion points
	Pm:=trim (E+Pmin);
	-- Remove the 2- and 3-torsion points to obtain the honest 6-torsion points
	compPm:=primaryDecomposition Pm;
	--<< "mu=" << mu << endl;
	P:=saturate(E+Q',E+Q);
	compP':=primaryDecomposition P;
	compP:=compP';
	for j from 0 to #compP-1 do (
	    if radical (compP'#j) !=compP'#j then (
		compP=toList (set compP-set {compP'#j});
		);
	    );
	if #compPm!=3 then mu=mu else (
	    i:=0;
	    while i<#compP and not isGood do (
		if degree compP#i!=1 then i=i+1 else (
		    -- Select the first two 2-torsion point and a 6-torsion point
		    T:={compPm#0,compPm#1,compP#i};
		    L:=for i from 0 to #T-1 list transpose syz contract(vars P4,transpose gens T#i);
		    -- Evaluate the Moore matrix 'M' at the first two 2-torsion points and the 6-torsion point to find three 5x5 matrices with linear entries and form a 5x15 matrix 'sigma'
		    M1:=sub(M,L#0);
		    M2:=sub(M,L#1);
		    M3:=sub(M,L#2);
		    sigma:=map(P4^{5:6},,sub(M1|M2|M3,P4));
		    fsigma:=res coker sigma;
		    -- Check whether 'sigma' has a minimal free resolution of the desired type
		    if (tally degrees source fsigma.dd_2)_{-4}===10 then (
			ff:=res coker map(P4^{1:8},,vars P4);
			p1:=transpose ((random(target transpose ff.dd_5,target transpose fsigma.dd_3)*transpose fsigma.dd_3) // transpose ff.dd_5);
			p2:=random(target p1,P4^{5:4});
			phi:=fsigma.dd_3 | (p2 | p1);
			-- Define 'X' as the quotient of the first syzygy module of the cokernel of 'sigma'
			X:=trim ideal syz(transpose phi);
			isGood=true;
			) else i=i+1
		    );
		);
	    );
	mu=mu+1;
	-- If 'mu' becomes bigger than or equal two, then it means the script failed to find a bielliptic surface and returns 'null' 
	if mu>=p then return null;
	);
     -- Check whether 'X' is a surface with the desired degree and sectional genus 
    assert(dim X==3 and degree X==10 and sectionalGenus X==6);
    X
    )



biellipticSurfaceD15=method()
-- Bielliptic surface of degree 15 (B5.1)
--     PURPOSE : Construct a bielliptic surface, which is a nonsingular surface of degree 15 and sectional genus 21
--       INPUT : 'P4', the homogeneous coordinate ring of projective fourspace over the finite field of characteristic p
--      OUTPUT : Ideal of the bielliptic surface or 'null' if the function failed to find a surface
-- DESCRIPTION : This function first forms the Moore matrix, uses it to define a finite module, and a bielliptic surface as the degeneracy locus of a map from a vector bundle to the sheafified first syzygy module
-- DESCRIPTION : This function first forms the Moore matrix, uses it to define a finite module, and a bielliptic surface as the degeneracy locus of a map from a vector bundle to the sheafified first syzygy module
--     COMMENT : The function could fail to find a surface, and if it fails, it return 'null' (this happens especually if 'p' is small) However, the function seems to find a surface when 'p' is large 

biellipticSurfaceD15(PolynomialRing):=P4->(
    z:=symbol z;
    S:=P4[z_0..z_4];
    -- Form the Moore matrix 'M'
    M:=matrix table(5,5,(i,j)->P4_((quotientRemainder(3*i+3*j,5))#1)*z_((quotientRemainder(3*i-3*j,5))#1));
    -- 'p' denotes the characteristic of 'P4'
    p:=char (coefficientRing P4);
    -- Define the eigenspace 'Pmin' corresponding to the eigenvalue 1 of the involution
    Pmin:=ideal(P4_1-P4_4,P4_2-P4_3);
    -- Define the quadric cone described in [ADHPR, Proposition 4.13] 
    Q:=ideal (P4_0^2+(P4_1+P4_4)*(P4_2+P4_3));
    -- Define the octic hypersurface described in [ADHPR, Proposition 4.19 (iii)] 
    --Q':=ideal((P4_0*(P4_2*P4_4^2-P4_1^2*P4_3))^2+(P4_3*(P4_0*P4_2^2-P4_4^2*P4_1)+P4_2*(P4_4*P4_1^2-P4_3^2*P4_0))*(P4_1*(P4_3*P4_0^2-P4_2^2*P4_4)+P4_4*(P4_1*P4_3^2-P4_0^2*P4_2)));
    Q':=ideal((P4_0*(P4_2*P4_4^2-P4_1^2*P4_3))^2+(P4_3*(P4_0*P4_2^2-P4_4^2*P4_1)+P4_2*(P4_4*P4_1^2-P4_3^2*P4_0))*(P4_1*(P4_3*P4_0^2-P4_2^2*P4_4)+P4_4*(P4_1*P4_3^2-P4_0^2*P4_2)));
    mu:=1;
    isGood:=false;
    -- Inside the following while loop, find an elliptic curve 'E' containing three ZZ/p-ratiinal nontrivial 2-torsion points and one F_p rational nontrivial 6-torsion point  
    while not isGood and mu<p do (
	E:=ideal for i from 0 to 4 list -mu*P4_((quotientRemainder(i,5))#1)^2-mu^2*P4_((quotientRemainder(i+1,5))#1)*P4_((quotientRemainder(i+4,5))#1)+P4_((quotientRemainder(i+2,5))#1)*P4_((quotientRemainder(i+3,5))#1);
	-- Check whether E is singular
	singE:=singularLocus E;
	c:=codim singE;
	if c!=5 then mu=mu+1;
        -- If E is nonsingular, take the intersection of 'E' with 'Pmin' to find nontrivial 2-torsion points
	--<< "mu=" << mu << endl;
	P:=saturate(E+Q',E+Q);
	compP':=primaryDecomposition P;
	compP:=compP';
	-- Remove the 2- and 3-torsion points to obtain the honest 6-torsion points
	for k from 0 to #compP-1 do (
	    if degree compP'#k > 1 then (
		compP=toList (set compP-set {compP'#k});
		);
	    );
	if #compP<3 then mu=mu else (
	    i:=1;
	    while i<#compP-1 and not isGood do (
		j:=i+1;
		while not isGood and j<#compP do (
		-- Select the first 6-torsion ppioints and then two 6-torsion point from 'compP'
		T:={compP#0,compP#i,compP#j};
		L:=for l from 0 to #T-1 list transpose syz contract(vars P4,transpose gens T#l);
		-- Evaluate the Moore matrix 'M' at the three 6-torsion points and the 6-torsion point to find three 5x5 matrices with linear entries and form a 5x15 matrix 'sigma'
		M1:=sub(M,L#0);
		M2:=sub(M,L#1);
		M3:=sub(M,L#2);
		sigma:=map(P4^{5:6},,sub(M1|M2|M3,P4));
		fsigma:=res coker sigma;
		-- Check whether 'sigma' has a minimal free resolution of the desired type
		if (tally degrees target fsigma.dd_3)_{-4}!=10 or (tally degrees target fsigma.dd_3)_{-3}!=1 then j=j+1 else (
		    X:=trim ideal syz transpose ((transpose (fsigma.dd_2)) | random(target transpose fsigma.dd_2,P4^{20:-2}));
		    isGood=true;
		    );
		    );
		i=i+1;
		);
	    );
	mu=mu+1;
	-- If 'mu' becomes bigger than or equal two, then it means the script failed to find a bielliptic surface and returns 'null' 
	if mu>=p then return null;
	);
    -- Check whether 'X' is a surface with the desired degree and sectional genus 
    assert(dim X==3 and degree X==15 and sectionalGenus X==21);
    X)




abelianSurfaceD10=method()
-- Abelian surface of degree 10 obtained as the zero scheme of a global section of the HM bundle (B6.1)
--     PURPOSE : Construct a nonsingular abelian surface of degree 10 and sectional genus 6
--       INPUT : 'P4', the homogeneous coordinate ring of projective fourspace 
--      OUTPUT : Ideal of the abelian surface of degree 10
-- DESCRIPTION : This function the ideal of an abalian surface as the zero scheme of a global section of the Horrocks-Mumford bundle
--     COMMENT : This function uses the BGG package

abelianSurfaceD10(PolynomialRing):=P4 -> (
    KK:=coefficientRing P4;
    e:=symbol e;
    -- Define an exterior algebra
    E:=KK[e_0..e_4,SkewCommutative=>true];
    -- Define morphisms 'alpha' and 'alphad' over 'E'
    alphad:=map(E^{5:0},E^{2:-2},{{e_4*e_1,e_2*e_3},{e_0*e_2,e_3*e_4},{e_1*e_3,e_4*e_0},{e_2*e_4,e_0*e_1},{e_3*e_0,e_1*e_2}});
    alpha:=syz alphad;
    -- Construct a Beilison monad; we use the command 'beilinson' to return the associated maps between direct sums of exterior powers of cotangent bundles
    alphad=beilinson(alphad,P4);
    alpha=beilinson(alpha,P4);
    -- Compute the homology of the monad, which is the Horrock-Mumford bundle 
    K:=prune homology(alphad,alpha);
    -- Define a variety 'X' as the dependency locus of two global sections of 'K'
    X:=trim ideal syz transpose (presentation K | random(source gens K,P4^{1:-3}));
    -- Check whether 'X' is a surface with the desired degree and sectional genus
    assert(dim X==3 and degree X==10 and sectionalGenus X==6);    X)

horrocksMumfordSurface=method()

horrocksMumfordSurface(PolynomialRing) := P4 -> abelianSurfaceD10(P4)


abelianSurfaceD15=method()
-- Abelian surface of degree 15, which is linkned to the HM abelian surface (B6.2)
--     PURPOSE : Construct a nonsingular abelian surface of degree 15 and sectional genus 21
--       INPUT : 'P4', the homogeneous coordinate ring of projective fourspace 
--      OUTPUT : Ideal of the abelian surface of degree 15
-- DESCRIPTION : This function constructs the abelian surface as the surface residual to the abelian surface of degree 10 in the (5,5) complete intersection
--     COMMENT : This function uses the BGG package and 'abelianSurfaceD10'

abelianSurfaceD15(PolynomialRing):=P4 -> (
    -- Use 'abelianSurfaceD10' to construct an abelian surface 'Y' of deegree 10
    Y:=abelianSurfaceD10(P4);
    -- Choose two quintics containing 'Y' to define a complete intersetion 'V'  
    V:=ideal (gens Y*random(source gens Y,P4^{2:-5}));
    -- Define 'X' resitual to 'Y' in 'V'
    X:=V:Y;
    -- Check whether 'X' is a surface with the desired degree and sectional genus
    assert(dim X==3 and degree X==15 and sectionalGenus X==21);
    X)


abelianSurfaceD15S21Popescu=method()
-- Abelian surface of degree 15 and sectional genus 21 (15.B1: Syz_2(N) is incorrect)
--     PURPOSE : Construct a nonsingular abelian surface of degree 15 and sectional genus 21
--       INPUT : 'P4', the homogeneous coordinate ring of projective fourspace 
--      OUTPUT : Ideal of the abelian surface of degree 15
-- DESCRIPTION : This function constructs the abelian surface as the dependency locus of two sections of a rank three vector bundle

abelianSurfaceD15S21Popescu(PolynomialRing):=P4->(
    -- Define three Moore matrices 'M1,' 'M2,' and 'M3'
    z:=symbol z;
    S:=P4[z_0..z_4];
    M:=matrix table(5,5,(i,j)->P4_((quotientRemainder(3*i+3*j,5))#1)*z_((quotientRemainder(i-j,5))#1));
    m1:=random(S^1,S^3)*matrix{{1,0,0,0,0},{0,1,0,0,1},{0,0,1,1,0}};
    m2:=random(S^1,S^2)*matrix{{0,0,1,-1,0},{0,1,0,0,-1}};
    m3:=random(S^1,S^2)*matrix{{0,0,1,-1,0},{0,1,0,0,-1}};
    M1:=sub(M,m1);
    M2:=sub(M,m2);
    M3:=sub(M,m3);
    -- Concatenate 'M1,' 'M2,' and 'M3' horizontally
    sigma:=map(P4^{5:6},,sub(M1|M2|M3,P4));
    fsigma:=res coker sigma;
    ff:=res cokernel transpose fsigma.dd_5;
    -- Construct 'X' as the degeneracy locus of a generic map from 15O_P4(-2) ++ O_P4(-3) to the sheafified second syzygy module of the dual of 'sigma'
    X:=trim ideal syz(transpose (ff.dd_4 |random(target ff.dd_4,P4^{15:-2,-3})),DegreeLimit=>2);
    -- Check whether 'X' is a surface with the desired degree and sectional genus
    assert(dim X==3 and degree X==15 and sectionalGenus X==21);
    X)


K3surfaceD7=method()
-- K3 surface of degree 7 and sectional genus 5 (B4.3)
--     PURPOSE : Construct a nonsingular K3 surface of degree 7 and sectional genus 5
--       INPUT : 'P4', the homogeneous coordinate ring of projective fourspace 
--      OUTPUT : Ideal of the K3 surface of degree 7
-- DESCRIPTION : This function constructs the K3 surface as the degeneracy locus of a map between two vector bundles

K3surfaceD7(PolynomialRing):=P4 -> (
    -- Define a variety 'X' as the degeneracy locus of a generic map from O_PA(-1) ++ O_PA(-2) to 3O_PA 
    X:=minors(2,random(P4^{3:0},P4^{-1,-2}));
    -- Check whether 'X' is a surface with the desired degree and sectional genus
    assert(dim X==3 and degree X==7 and sectionalGenus X==5);
    X)


K3surfaceD8=method()
-- K3 surface of degree 8 and sectional genus 6 (B4.4)
--     PURPOSE : Construct a nonsingular K3 surface of degree 8 and sectional genus 6
--       INPUT : 'P4', the homogeneous coordinate ring of projective fourspace 
--      OUTPUT : Ideal of the K3 surface of degree 8
-- DESCRIPTION : This function constructs the K3 surface as the degeneracy locus of a map between two vector bundles

K3surfaceD8(PolynomialRing) := P4 -> (
    -- Compute the koszul complex of the variables of 'P4'
    kos:=res coker vars P4;
    -- Construct 'X' as the degeneracy locus of a generic map from O_P4(-3) ++ 2O_P4(-2) to the cotangent bundle 
    X:=ideal syz transpose (kos.dd_3 | random(target kos.dd_3,P4^{2:-2,-3}));
    -- Check whether 'X' is a surface with the desired degree and sectional genus
    assert(dim X==3 and degree X==8 and sectionalGenus X==6);
    X)


K3surfaceD9=method()
-- K3 surface of degree 9 and sectional genus 8 (B4.5)
--     PURPOSE : Construct a nonsingular K3 surface of degree 9 and sectional genus 8
--       INPUT : 'P4', the homogeneous coordinate ring of projective fourspace 
--      OUTPUT : Ideal of the K3 surface of degree 9
-- DESCRIPTION : This function constructs the K3 surface as the degeneracy locus of a map between two vector bundles

K3surfaceD9(PolynomialRing) := P4 -> (
    -- Compute the koszul complex of the variables of 'P4'
    kos:=res coker vars P4;
    -- Define the direct sum 'f' of the fourth exterior power of the cotangent bundle and O_PA(_4)
    f:=kos.dd_4 ++ map(P4^{-4},P4^{-4},1);
    -- Define 'X' as the degeneracy locus of a general map from 'f' to 6O_P4(-3)
    X:=trim ideal syz transpose (random(P4^{6:-3},target f)*f);
    -- Check whether 'X' is a surface with the desired degree and sectional genus
    assert(dim X==3 and degree X==9 and sectionalGenus X==8);
    X)


K3surfaceD10S9SL1=method()
-- K3 surface of degree 10 and sectional genus 9 with one 6-secant line (this script is a little cheating) (B4.6)
--     PURPOSE : Construct a nonsingular K3 surface of degree 10 and sectional genus 9 with one 6-secant line
--       INPUT : 'P4', the homogeneous coordinate ring of projective fourspace 
--      OUTPUT : Ideal of the K3 surface of degree 10 with one 6-secant line
-- DESCRIPTION : This function constructs the ideal of the K3 surface as the homology of a Beilinson monad
--     COMMENT : This function uses the BGG package

K3surfaceD10S9SL1(PolynomialRing) := P4 -> (
    KK:=coefficientRing P4;
    e:= symbol e;
    -- Define an exterior algebra
    E:=KK[e_0..e_4,SkewCommutative=>true];
    -- Define morphisms 'f' and 'g' of modules over 'E'
    f:=map(E^{1:0},E^{1:-1},0) | map(E^{1:0},E^{2:-1},{{e_0,e_1}}) | map(E^{1:0},E^{1:0},0);
    g:=(syz f)*random(source syz f,E^{-2,-3,-4});
    -- Construct a Beilison monad; we use the command 'beilinson' to return the associated maps between direct sums of exterior powers of cotangent bundles
    beta:=beilinson(f,P4);
    alpha:=beilinson(g,P4);
    -- Compute the homology 'I' of the Beilinson monad 
    I:=prune homology(beta,alpha);
    -- Define 'X' by 'I'
    X:=trim ideal syz(transpose presentation I,DegreeLimit=>4);
    -- Check whether 'X' is a surface with the desired degree and sectional genus
    assert(dim X==3 and degree X==10 and sectionalGenus X==9);
    X)

-- K3 surface of degree 10 and sectional genus 9 with three secant lines (B4.7)
--     PURPOSE : Construct a nonsingular K3 surface of degree 10 and sectional genus 9 with three 6-secant lines
--       INPUT : 'P4', the homogeneous coordinate ring of projective fourspace 
--      OUTPUT : Ideal of the K3 surface of degree 10 with one 6-secant line
-- DESCRIPTION : This function constructs the ideal of the K3 surface as the degeneracy locus of a map between two vector bundles

K3surfaceD10S9SL3=method()
K3surfaceD10S9SL3(PolynomialRing) := P4 -> (
    -- Compute the koszul complex of the variables of 'P4'
    kos:=res coker vars P4;
    -- Compute the presentation 'omega' of the third exterior power of the cotangent bundle twisted by 3 
    omega:=map(P4^{5:-1},,kos.dd_5);
    -- Choose a map 'f' from 2O_P4(1) ++ 4O_P4 t0 2O_P4(2) randomley 
    f:= random(P4^{1:2},P4^{2:1,4:0});
    ff:=res coker f;
    -- Define a map 'r' from O_P4(-1) ++ the first exterior power of the cotangent bundle twisted by 3 to the direct sum of the first syzygy module of 'f' and O_PA randomly
    p1:=transpose ((random(target transpose omega,target transpose ff.dd_3)*transpose ff.dd_3) // transpose omega);
    p2:=random(target p1,P4^{1:-1});
    q1:=random(P4^{1:0},P4^{10:0})*map(P4^{10:0},,kos.dd_4);
    q2:=random(P4^{1:0},P4^{1:-1});
    p:=(p2 | p1)||(q2 | q1);
    q:=ff.dd_2++map(P4^{1:0},P4^{1:0},1);
    r:=(syz q) | p;
    -- Define 'X' as the cokernel of 'r'
    X:=trim ideal syz transpose r;
    -- Check whether 'X' is a surface with the desired degree and sectional genus
    assert(dim X==3 and degree X==10 and sectionalGenus X==9);
    X)


H1module = method()
H1module(PolynomialRing,ZZ):= (P4,a)->(
    -- This function uses Description (3.10) in Sorin Popescu's thesis
    var:=vars P4;
    y:=first entries var;
    phi1:=map(P4^{2:5},,var || matrix {for i from 0 to 4 list random(0,P4)*y#i});
    pts:=ideal var;
    if a == 0 then pts=pts else 
    for i from 1 to a list pts = intersect(pts,ideal toList (set y-{y#(i-1)})); 
    phi2:=map(P4^{2:5},,matrix{{0,0}}||(gens pts)*random(source gens pts,P4^{2:-1}));
    phi:=phi1 | phi2 | random(P4^{2:5},P4^{a:3});
    fphi:=res coker phi;
    ftphi:=res coker transpose fphi.dd_5;
    ftphi.dd_3
    )

K3surfaceD11S11SLn=method()
-- K3 surface of degree 11 and sectional genus 11 witha 6-secant lines (B4.8-11)
--     PURPOSE : Construct a nonsingular K3 surface of degree 11 and sectional genus 11 with 'n' 6-secant lines
--       INPUT : 'P4', the homogeneous coordinate ring of projective fourspace and an integer between 0 and 3 
--      OUTPUT : Ideal of the K3 surface of degree 10 with 'n' 6-secant lines
-- DESCRIPTION : This function constructs the ideal of the K3 surface as the degeneracy locus of a map between two vector bundles
--     COMMENT : This function uses 'H1module,' a command that takes "P4' and an integer between 0 and 3 and returns the H1 module of the ideal sheaf of the surface 

K3surfaceD11S11SLn(PolynomialRing,ZZ):=(P4,n)->(
    var:=vars P4;
    -- Calculate the direct sum of two Koszul complexes
    kos:=res coker (var++var);
    -- Denote by 'Omega' the third syzygy module sheaf of 'var++var'
    omega:=map(P4^{10:-1},,kos.dd_5);
    -- Use 'H1module' to construct the sheafified first syzygy module a module of finite length 
    f:=H1module(P4,n);
    ff:=res coker f;
    -- Choose randomly a map 'p' from the direct sum of O_P4(-1) and the two copies of the third exterior power of the cotangent bundle twisted by 3 to the first syzygy module sheaf of 'coker f'
    p1:=transpose ((random(target transpose omega,target transpose ff.dd_1)*transpose ff.dd_1) // transpose omega);
    p2:=random(target p1,P4^{1:-1});
    p:=ff.dd_1 | (p2 | p1);
    -- Construct 'X' as the degeneracy locus of 'p'
    X:=trim ideal syz(transpose p,DegreeLimit=>4);
    -- Check whether 'X' is a surface with the desired degree and sectional genus
    assert(dim X==3 and degree X==11 and sectionalGenus X==11);
    X)

-- K3 surface of degree 11 and sectional genus 12 (B4.12)
--     PURPOSE : Construct a nonsingular K3 surface of degree 11 and sectional genus 12 
--       INPUT : 'P4', the homogeneous coordinate ring of projective fourspace 
--      OUTPUT : Ideal of the K3 surface of degree 11 and sectional genus 12
-- DESCRIPTION : This function constructs the K3 surface as the degeneracy locus of a map between two vector bundles

K3surfaceD11S12=method()
K3surfaceD11S12(PolynomialRing) := P4 -> (
    -- Compute the koszul complex of the variables of 'P4'
    kos:=res coker vars P4;
    -- Construct the presentation 'f' of the direct sum of 2O_P4 and the direct sum of two copies of the second exterior power of the cotangent bundle twisted by 2 
    f:=map(P4^{2:-1},P4^{2:-1},1)++map(P4^{20:-1},,kos.dd_3++kos.dd_3);
    syzf:=syz f;
    -- Define a map 'g' from the direct sum of O_P4(-1) and the direct sum of 3 copies of the third exterior power of the cotangent bundle twisted by 3 via exterior algebra
    KK:=coefficientRing P4;
    e:= symbol e;
    E:=KK[e_0..e_4,SkewCommutative=>true];
    g:=map(target syzf,,beilinson(random(E^{2:0,2:-2},E^{3:-3,-4}),P4));
    -- Construct 'X' as the cokernel of 'g'
    X:=trim ideal syz transpose (syzf | g);
    -- Check whether 'X' is a surface with the desired degree and sectional genus
    assert(dim X==3 and degree X==11 and sectionalGenus X==12);
    X)

-- K3 surface of degree 12 and sectional genus 14 (B4.13)
--     PURPOSE : Construct a nonsingular K3 surface of degree 12 and sectional genus 14
--       INPUT : 'P4', the homogeneous coordinate ring of projective fourspace 
--      OUTPUT : Ideal of the K3 surface of degree 12 
-- DESCRIPTION : This function constructs the K3 surface as the surface residual to a regular elliptic surface of degree 12 in the (5,5) complete intersection
--     COMMENT : This function uses 'BGG'

K3surfaceD12=method()
K3surfaceD12(PolynomialRing) := P4 -> (
    -- Compute the koszul complex of the variables of 'P4'
    kos:=res coker vars P4;
    -- Find a set 'f' of generators for the direct sum 'F' of three copies of the second exterior power of the cotangent bundle 
    f:=map(P4^{30:-1},,kos.dd_3++kos.dd_3++kos.dd_3);
    syzf:=syz f;
    -- Define a map 'g' from the direct sum of O_P4(-1) and the four copies of the third exterior power of the cotangent bundle to 'F'
    KK:=coefficientRing P4;
    e:= symbol e;
    E:=KK[e_0..e_4,SkewCommutative=>true];
    g:=map(target syzf,,beilinson(random(E^{3:-2},E^{4:-3,-4}),P4));
    -- Construct 'X' as the degeneracy locus of 'g'
    X:=trim ideal syz transpose (syzf | g);
    -- Check whether 'X' is a surface with the desired degree and sectional genus
    assert(dim X==3 and degree X==12 and sectionalGenus X==14);
    X)

-- K3 surface of degree 13 and sectional genus 16 (B4.14)
--     PURPOSE : Construct a nonsingular K3 surface of degree 13 and sectional genus 16
--       INPUT : 'P4', the homogeneous coordinate ring of projective fourspace 
--      OUTPUT : Ideal of the K3 surface of degree 13 
-- DESCRIPTION : This function constructs the K3 surface as the surface residual to a regular elliptic surface of degree 12 in the (5,5) complete intersection
--     COMMENT : This function uses 'regularEllipticSurfaceD12'

K3surfaceD13=method()
K3surfaceD13(PolynomialRing):=P4->(
    -- Use 'regularEllipticSurfaceD12'to construct a regular elliptic surface of degree 12
    Y:=regularEllipticSurfaceD12(P4);
    -- Choose two quintics containing 'Y' to define a complete intersection 'V' 
    V:=ideal ((gens Y)*random(source gens Y,P4^{2:-5}));
    -- Define 'X' resitual to 'Y' in 'V'
    X:=V:Y;
    -- Check whether 'X' is a surface with the desired degree and sectional genus
    assert(dim X==3 and degree X==13 and sectionalGenus X==16);
    X)

-- K3 surface of degree 14 and sectional genus 19 (B4.15)
--     PURPOSE : Construct a nonsingular K3 surface of degree 14 and sectional genus 19
--       INPUT : 'P4', the homogeneous coordinate ring of projective fourspace 
--      OUTPUT : Ideal of the K3 surface of degree 14
-- DESCRIPTION : This function constructs the K3 surface as the degeneracy locus of a map between two vector bundles

K3surfaceD14=method()
K3surfaceD14(PolynomialRing):=P4->(
    -- Choose four random planes
    P:=for i from 0 to 3 list random(P4^{1:4},P4^{2:3});
    -- Define the direct sum of the four Koszul complexes of the generators for 'P#i'  
    alpha:=P#0;
    for i from 1 to 3 do alpha = alpha++P#i;
    -- Use 'alpha' to define a map from 8O_P4(3) ++ 2O_P4(2) to 3O_P4 
    phi1:=random(P4^{3:4},P4^{4:4})*alpha;
    phi2:=random(target phi1,P4^{2:2});
    phi:=phi1|phi2;
    -- Calculate the dual of 'coker phi' 
    fphi:=res coker phi;
    ftphi:=res coker transpose fphi.dd_5;
    -- Define 'X' as the degeneracy locus of a generic map from the second syzygy bundle of 'ftphi.dd_1' and O_P4(-1) ++ 15O_P4
    X:=ideal syz transpose (ftphi.dd_4 | random(target ftphi.dd_4,P4^{15:0,1:-1}));
    -- Check whether 'X' is a surface with the desired degree and sectional genus
    assert(dim X==3 and degree X==14 and sectionalGenus X==19);
    X)

-- Elliptic surface of degree 7 and sectional genus 6 (B7.1)
--     PURPOSE : Construct a nonsingular elliptic surface of degree 7 and sectional genus 6
--       INPUT : 'P4', the homogeneous coordinate ring of projective fourspace 
--      OUTPUT : Ideal of the elliptic surface of degree 7
-- DESCRIPTION : This function constructs the elliptic surface as the degeneracy locus of a map between two vector bundles

ellipticSurfaceD7=method()
ellipticSurfaceD7(PolynomialRing) := P4 -> (
    -- Construct 'X' as the dependency locus of a generic map from 2O_P4(-2) to 2O_P4(-1) ++ O_P4(1)  
    X:=minors(2,random(P4^{1:1,2:-1},P4^{2:-2}));
    -- Check whether 'X' is a surface with the desired degree and sectional genus
    assert(dim X==3 and degree X==7 and sectionalGenus X==6);
    X)

-- Elliptic surface of degree 8 and sectional genus 7 (B7.2)
--     PURPOSE : Construct a nonsingular elliptic surface of degree 8 and sectional genus 7
--       INPUT : 'P4', the homogeneous coordinate ring of projective fourspace 
--      OUTPUT : Ideal of the elliptic surface of degree 8
-- DESCRIPTION : This function constructs the elliptic surface as the degeneracy locus of a map between two vector bundles

ellipticSurfaceD8=method()
ellipticSurfaceD8(PolynomialRing) := P4 -> (
    -- Construct 'X' as the dependency locus of a generic map from 2O_P4(-2) to O_P4 ++ 2O_P4(1)  
    X:=minors(2,random(P4^{2:1,1:0},P4^{2:-1}));
    -- Check whether 'X' is a surface with the desired degree and sectional genus
    assert(dim X==3 and degree X==8 and sectionalGenus X==7);
    X)

-- Elliptic surface of degree 9 and sectional genus 7 (B7.3)
--     PURPOSE : Construct a nonsingular elliptic surface of degree 9 and sectional genus 7
--       INPUT : 'P4', the homogeneous coordinate ring of projective fourspace 
--      OUTPUT : Ideal of the elliptic surface of degree 9
-- DESCRIPTION : This function constructs the elliptic surface as the degeneracy locus of a map between two vector bundles
--     COMMENT : This function uses the BGG package

ellipticSurfaceD9=method()
ellipticSurfaceD9(PolynomialRing) := P4 -> (
    -- Compute the koszul complex of the variables of 'P4'
    kos:=res coker vars P4;
    -- Construct a set of generatros for the direct sum of three copies of the cotangent bundle twisted by -1 and two copies of O_P4(-1)
    f:=map(P4^{2:-1},P4^{2:-1},1)++map(P4^{15:-1},,kos.dd_2++kos.dd_2++kos.dd_2);
    -- Find the presentation of 'image f' 
    syzf:=syz f;
    -- Choose a map from the direct sum of O_P4(-3) and two copies of the second exterior power of the cotangent bundle twisted by -1 to 'image f'
    KK:=coefficientRing P4;
    e:= symbol e;
    E:=KK[e_0..e_4,SkewCommutative=>true];
    g:=map(target syzf,,beilinson(random(E^{2:0,3:-1},E^{2:-2,-4}),P4));
    -- Construct 'X' as the dependency locus of 'g' 
    X:=trim ideal syz transpose (syzf | g);
    -- Check whether 'X' is a surface with the desired degree and sectional genus
    assert(dim X==3 and degree X==9 and sectionalGenus X==7);
    X)

-- Elliptic surface of degree 10 and sectional genus 9 (B7.4)
--     PURPOSE : Construct a nonsingular elliptic surface of degree 10 and sectional genus 9
--       INPUT : 'P4', the homogeneous coordinate ring of projective fourspace 
--      OUTPUT : Ideal of the elliptic surface of degree 9
-- DESCRIPTION : This function constructs the elliptic surface as the homology of a Beilinson monad 
--     COMMENT : This function uses the BGG package

ellipticSurfaceD10S9=method()
ellipticSurfaceD10S9(PolynomialRing) := P4 -> (
    KK:=coefficientRing P4;
    e:= symbol e;
    -- Define an exterior algebra
    E:=KK[e_0..e_4,SkewCommutative => true];
    -- Define morphisms 'f' and 'g' over 'E'  
    f:=map(E^{1:0},E^{3:-1},{{e_0..e_2}}) | map(E^{1:0},E^{1:0},0);
    g:=(syz f)*random(source syz f,E^{-2,-3,-4});
    -- Construct a Beilison monad; we use the command 'beilinson' to return the associated maps between direct sums of exterior powers of twisted cotangent bundles
    beta:=beilinson(f,P4);
    alpha:=beilinson(g,P4);
    -- Compute the homology 'I' of the Beilinson monad
    I:=prune homology(beta,alpha);
    -- Construct 'X' as the scheme of 'I' 
    X:=trim ideal syz transpose presentation I;
    -- Check whether 'X' is a surface with the desired degree and sectional genus
    assert(dim X==3 and degree X==10 and sectionalGenus X==9);
    X)
    
-- Elliptic surface of degree 10 and sectional genus 10 (B7.5)
--     PURPOSE : Construct a nonsingular elliptic surface of degree 10 and sectional genus 10
--       INPUT : 'P4', the homogeneous coordinate ring of projective fourspace 
--      OUTPUT : Ideal of the elliptic surface of degree 10
-- DESCRIPTION : This function constructs the elliptic surface as the degeneracy locus of a map between two vector bundles
--     COMMENT : This function uses the BGG package

ellipticSurfaceD10S10=method()
ellipticSurfaceD10S10(PolynomialRing) := P4 -> (
    -- Compute the koszul complex of the variables of 'P4'
    kos:=res coker vars P4;
    -- Define a map 'f' whose image is the direct sum of three copies of O_P4 and the cotangent bundle
    f:=map(P4^{3:-1},P4^{3:-1},1)++map(P4^{5:-1},,kos.dd_2);
    syzf:=syz f;
    -- Choose a map 'g' from the direct sum of 2O_P4(-2) and the third exterior power of the cotangent bundle  
    KK:=coefficientRing P4;
    e:= symbol e;
    E:=KK[e_0..e_4,SkewCommutative=>true];
    g:=map(target syzf,,beilinson(random(E^{3:0,1:-1},E^{1:-3,2:-4}),P4));
    -- Construct 'X' as the degeneracy locus of 'g' 
    X:=trim ideal syz transpose (syzf | g);
    -- Check whether 'X' is a surface with the desired degree and sectional genus
    assert(dim X==3 and degree X==10 and sectionalGenus X==10);
    X)

-- Elliptic surface of degree 11 and sectional genus 12 (B7.6)
--     PURPOSE : Construct a nonsingular elliptic surface of degree 11 and sectional genus 12
--       INPUT : 'P4', the homogeneous coordinate ring of projective fourspace 
--      OUTPUT : Ideal of the elliptic surface of degree 10
-- DESCRIPTION : This function constructs the elliptic surface as the degeneracy locus of a map between two vector bundles
--     COMMENT : This function uses the BGG package

ellipticSurfaceD11S12=method()
ellipticSurfaceD11S12(PolynomialRing):=P4 -> (
    -- Compute the koszul complex of the variables of 'P4'
    kos:=res coker vars P4;
    -- Define a map 'f' whose image is the direct sum of O_P4(-1), the cotangent bundle, and its second exterior power
    f:=map(P4^{-1},P4^{-1},1)++map(P4^{15:-1},,kos.dd_2++kos.dd_3);
    syzf:=syz f;
    -- Choose a map 'g' from the direct sum of 2O_P4(-2) and the third exterior power of the cotangent bundle  
    KK:=coefficientRing P4;
    e:= symbol e;
    E:=KK[e_0..e_4,SkewCommutative=>true];
    g:=map(target syzf,,beilinson(random(E^{0,-1,-2},E^{2:-3,2:-4}),P4));
    -- Construct 'X' as the degeneracy locus of 'g' 
    X:=trim ideal syz transpose (syzf | g);
    -- Check whether 'X' is a surface with the desired degree and sectional genus
    assert(dim X==3 and degree X==11 and sectionalGenus X==12);
    X)

-- Elliptic surface of degree 12 and sectional genus 14 with no 6 secant line (B7.8)
--     PURPOSE : Construct a nonsingular elliptic surface of degree 12 and sectional genus 14
--       INPUT : 'P4', the homogeneous coordinate ring of projective fourspace 
--      OUTPUT : Ideal of the elliptic surface of degree 12
-- DESCRIPTION : This function constructs the elliptic surface as the homology of a Beilinson monad 
--     COMMENT : This function uses the BGG package

ellipticSurfaceD12S14L0=method()
ellipticSurfaceD12S14L0(PolynomialRing):=P4 -> (
    KK:=coefficientRing P4;
    e:= symbol e;
    -- Define an exterior algebra
    E:=KK[e_0..e_4,SkewCommutative => true];
    -- Choose morphisms 'f' and 'g' over 'E' randomly 
    f:=random(E^{1:0},E^{1:-1,2:-2});
    g:=(syz f)*random(source syz f,E^{3:-3,2:-4});
    -- Construct a Beilison monad; we use the command 'beilinson' to return the associated maps between direct sums of exterior powers of twisted cotangent bundles
    I:=prune homology(beilinson(f,P4),beilinson(g,P4));
    -- Construct 'X' as the scheme of 'I'
    X:=trim ideal syz (transpose presentation I,DegreeLimit=>4);
    -- Check whether 'X' is a surface with the desired degree and sectional genus
    assert(dim X==3 and degree X==12 and sectionalGenus X==14);
    X)

-- Elliptic surface of degree 12 and sectional genus 14 with infinitely many 6 secant line (B7.9)
--     PURPOSE : Construct a nonsingular elliptic surface of degree 12 and sectional genus 14 with infinitely many 6-secant lines
--       INPUT : 'P4', the homogeneous coordinate ring of projective fourspace 
--      OUTPUT : Ideal of the elliptic surface of degree 12
-- DESCRIPTION : This function constructs the elliptic surface as the homology of a Beilinson monad 
--     COMMENT : This function uses the BGG package

ellipticSurfaceD12S14Linfinite=method()
ellipticSurfaceD12S14Linfinite(PolynomialRing):=P4 -> (
    KK:=coefficientRing P4;
    e:= symbol e;
    -- Define an exterior algebra
    E:=KK[e_0..e_4,SkewCommutative => true];
    -- Choose a specific morphism 'f' over 'E' 
    f:=map(E^{1:0},E^{1:-1,2:-2},{{e_2,e_0*e_1,0}});
    -- Choose a morphism 'g' over E randomly
    g:=(syz f)*random(source syz f,E^{3:-3,2:-4});
    -- Construct a Beilison monad; we use the command 'beilinson' to return the associated maps between direct sums of exterior powers of twisted cotangent bundles
    I:=prune homology(beilinson(f,P4),beilinson(g,P4));
    -- Construct 'X' as the scheme of 'I'
    X:=trim ideal syz (transpose presentation I,DegreeLimit=>4);
    -- Check whether 'X' is a surface with the desired degree and sectional genus
    assert(dim X==3 and degree X==12 and sectionalGenus X==14);
    X)




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
	TO unirationalFamiliesOfRationalSurfaces,
	TO schreyerSurfaces,
	TO aboRanestadSurfaces
        },
     SUBSECTION "Enriques and K3 surfaces",
     UL{
        TO enriquesSurfaceOfDegree9,
	TO enriquesSurfaceOfDegree10,
	TO enriquesSurfaceD11S10,
	TO K3surfaces,
        },
    SUBSECTION "Irregular surface",
     UL{
        TO quinticEllipticScroll,
	TO ellipticConicBundle,
	TO horrocksMumfordSurface,
	TO abelianSurfaceD15,
	TO abelianSurfaceD15S21Popescu,
	TO biellipticSurfaceD10,
	TO biellipticSurfaceD15,
        },
    SUBSECTION "Elliptic surfaces",
     UL{
        TO irregularEllipticSurfaceD12,
	TO regularEllipticSurfaceD12,
	TO surfacesOfKodairaDimension1,
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
Key => unirationalFamiliesOfRationalSurfaces,
Headline => "unirational families of rational surfaces",
   "Most of the families constructed in [DES], [Popescu1] and before are actually unirational. We list the link to the corresponding functions.
    An exception are certain families of Schreyer and Abo-Ranestad surfaces, where we only know that some of the families are unirational.",
   
   PARA{},
     SUBSECTION "non-degenerate rational surfaces in P4",
     UL{
        TO cubicScroll,
	TO delPezzoSurface,
	TO castelnuovoSurface,
	TO bordigaSurface,        
        TO ionescuOkonekSurface,
	TO degree8OkonekSurface,
	TO nonspecialAlexanderSurface,
	TO specialityOneAlexanderSurface,
	TO degree10DESSurface,
	TO degree10pi9RanestadSurface,
	TO degree10pi8RanestadSurface,
	TO popescuSurface,
	TO vBELSurface
        },
    PARA{},
     SUBSECTION "further families",
     UL{
        TO schreyerSurfaces,
	TO aboRanestadSurfaces
	}
}



document {
Key => schreyerSurfaces,
Headline => "functions concerning Schreyer surfaces (9 or 10 families)",
   "[Schreyer,1996] discovered 4 families of surfaces X in P4 with d=11, sectional genus pi=10 via a search over a finite field
   of which 3 families consist of rational surfaces. 
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
    
     SUBSECTION "lift to characteristic zero and unirational or nearly unirational families",
     UL{
	TO tangentDimension,
        TO unirationalConstructionOfSchreyerSurface,
	TO specialEnriquesSchreyerSurface,
	TO schreyerSurfaceWith2LinearSyzygies
        }        
}



document {
Key => aboRanestadSurfaces,
Headline => "functions concerning Abo-Ranestad surfaces ( 9 families)",
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
	TO get4x2Matrix,
        --TO singAboRanestadSurfacesStatistic,
        },
    
     SUBSECTION "lift to characteristic zero",
     UL{
	--TO tangentComputation,
	TO veroneseImagesInG25
        }        
}

document {
Key => K3surfaces,
Headline => "Known families of K3 surfaces",
   "Various family of non-minmal K3 surfaces are known.
    We enumerate the families by the degree D, the sectional genus S and
    their 6-secant behavious L. Note that a smooth surface in P4 is expected to have 
    finitely many 6-secants. If this number is finite, then Le Barz 6-secant formula
    computes sum of the number of 6-secants and the number of  of (-1) lines on the surface.
    Since every 6-secant line is contained in the zero locus of the the ideal generated by the quintics
    containg the surface, the number of 6-secant can often be determined from the equation
    of the surface, hence in that case we get information about the (-1)-Lines, ie. ,
    the curve contacted by the first adjunction map.",
    
   PARA{},
     SUBSECTION "K3 surfaces",
     UL{
        TO K3surfaceD7,
	TO K3surfaceD8,
	TO K3surfaceD9,
	TO K3surfaceD10S9SL1,
	TO K3surfaceD10S9SL3,
	-- TO H1module,
	TO K3surfaceD11S11SLn,
	TO K3surfaceD11S12,
	TO K3surfaceD12,
	TO K3surfaceD13,
	TO K3surfaceD14,      
        },
    PARA{},
     SUBSECTION "6-secants and adjunction",
     UL{
	TO LeBarzN6,
	TO adjunctionProcessData,
	},
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
 compute a Schreyer Surface with given the H^1-module of the ideal sheaf
Usage
 X = schreyerSurfaceFromModule M
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
 [schreyerSurfaceWith2LinearSyzygies,Smooth]
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
    (d,sg)=(degree X, sectionalGenus X)
    Ksquare(d,sg,1)==-6   
    LeBarzN6(d,sg,1)==10
    minimalBetti X
    betti(X5=ideal (gens X)_{0..4})
    betti(residual=X5:X)
    dim residual,degree residual
    tally apply(primaryDecomposition residual,c-> (
	(dim c, degree c, degree (c+X))))
  Text
    There are 6 six-secant lines grouped in Frobenius orbis.
    So there should be 4 (-1) lines. Indeed, the adjunction data say this.
    The last surface in the adjunction process is a conic bundle with
    6+8-5=9 singular fibers.

    The construction of X uses a special Hartshorne-Rao module M.   
  Example
    betti tateResolutionOfSurface X
    M=moduleFromSchreyerSurface X;
    minimalBetti M
    tangentDimension M==36
  Text
    Thus the space of good modules in the Grassmannian G(5,15) of dimension 50 is smooth of
    the expected codimension 14 at our point M.
    Hence X lifts to a surface defined over some number field, which gives a surface over
    CC.
SeeAlso
   adjunctionProcessData
   LeBarzN6
   Ksquare
   tateResolutionOfSurface
   moduleFromSchreyerSurface
   tangentDimension
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
 [schreyerSurface,Smooth]
 [schreyerSurface,Verbose]
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
 [findRandomSmoothSchreyerSurface,Verbose]
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

-* Abo-Ranestad surfaces *-

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
 [aboRanestadSurface,Special]
 [aboRanestadSurface,Smooth]
 [aboRanestadSurface,Verbose]
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
    elapsedTime (X,m4x2)=aboRanestadSurface(P4,4);  
    minimalBetti X
    singX=X+minors(2,jacobian X);
    dim saturate singX==-1
    (d,s)=(degree X, sectionalGenus X)
    LeBarzN6(d,s,1)==8
    Ksquare(d,s,1)==-12
    elapsedTime betti (T=tateResolutionOfSurface X)
    "elapsedTime (numList,L1,L2,J)=adjunctionProcess(X,3)";
    "numList=={(4, 12, 13), 4, (12, 24, 13), 12, (12, 16, 5), 0, (4, 4, 1)}";
  Text
     The last adjoint surface is a Del Pezzo surface of degree 4 in P4. Thus
     X is the blow-up in 12+9 points embedded by a linear system of class
     (12;4^5,2^12,1^4).
  
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
 [aboRanestadSurfaceFromMatrix,Smooth]
 [aboRanestadSurfaceFromMatrix,Verbose]
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
 get4x2Matrix
 (get4x2Matrix, Matrix, Number)
 [get4x2Matrix,Special]
Headline
 get a 4x2 matrix for an Abo Ranestad surface construction
Usage
 m4x2 = get4x2Matrix(m2x3,n)
Inputs
 m2x3:Matrix
  the 2x3 matrix in the Tate resolution of the desired Abo-Ranestad surface
 n:Number
  the desired number of intersection points in G(2,5)
Outputs
 m4x2:Matrix
  the 4x2 matrix of the Tate resolution of the desired Abo-Ranestad surface
Description
  Text
    In the Tate resolution of an Abo-Ranestad surface there is a 4x2 matrix m4x2 and a 2x3 matrix m2x3
    with linear entries over the exterior algbra. These matrices define rational maps P3 -> G(2,5) and P2 -> G(2,5)
    and the type of the surface depends on how these images intersect in the Grassmannin G(2,5). It turns out that the number of
    (-1) lines on the surface will coincides with the number of intersection points of the images + 1.
    The function returns for the normalized 2x3 matrix the desired 4x2 matrix.
  Example
    kk=ZZ/nextPrime 10^3
    P4=kk[x_0..x_4]
    E=kk[e_0..e_4,SkewCommutative=>true]
    m2x3=matrix{{e_0,e_1,e_3},{e_1,e_2,e_4}}
    m4x2=get4x2Matrix(m2x3,4)
    elapsedTime X=aboRanestadSurfaceFromMatrix(P4,m4x2,Verbose=>true);   
    elapsedTime betti(T=tateResolutionOfSurface X)
    "elapsedTime (numList,adjList,ptsList,J)=adjunctionProcess X;";
    "numList=={(4, 12, 13), 5, (12, 24, 13), 9, (12, 17, 6), 3, (5, 5, 1)}";
    B=new BettiTally from {(0,{0},0) => 1, (1,{2},2) => 5, (2,{3},3) => 5, (3,{5},5)=> 1}
    "minimalBetti J == B";    
SeeAlso
   aboRanestadSurfaceFromMatrix
   adjunctionProcess
   tateResolutionOfSurface
///
-* classical rational surfaces *-

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
    betti(X5=ideal (gens X)_{0..9})
    residual=X5:X;
    dim residual, degree residual, betti residual
    tally apply(primaryDecomposition residual,c->(dim c, degree c, betti c,
	    degree (c+X), betti saturate (c+X),
	    tally apply(primaryDecomposition saturate (c+X),d->(dim d, degree radical d))))
  Text
   There are 4 6-secant lines, 3 of them are in the plane which which intersects X
   in a plane quartic and three points. Hence there X contains two (-1)-lines.
   The adjunction process gives the data L0={(4, 10, 8), 2, (7, 14, 8), 1, (7, 12, 6), 0, (5, 7, 3)}.
   The last adjoint surface is a conic bundle in P5 with 9 singular fibers.
References
  Ranestad, DES
SeeAlso
   enriquesSurfaceOfDegree10
   adjunctionProcessData
///

-* possibly to add to degree10pi8RanestadSurface documentation
    "elapsedTime (L0,L1,L2,J)=adjunctionProcess(X);" -- 88.4042s elapsed
    "L0=={(4, 10, 8), 2, (7, 14, 8), 1, (7, 12, 6), 0, (5, 7, 3)}";
    "betti (fJ=res J) == new BettiTally from {(0,{0},0) => 1, (1,{2},2) => 3, (1,{3},3) => 3, (2,{3},3) => 2,(2,{4},4) => 6, (3,{5},5) => 3}"
    new BettiTally from {(0,{0},0) => 1, (1,{2},2) => 3, (1,{3},3) => 3, (2,{3},3) => 2,(2,{4},4) => 6, (3,{5},5) => 3}
    "(degree J, sectionalGenus J)==(7,3)";
    "fiber=trim ideal (random(kk^1,kk^3)*transpose fJ.dd_3);";
    "assert(fiber == ideal gens ring J)";
   Text
    It follows that the last adjoint surface X3 -> B is a conic bundle over a kk-rational conic B subset P2
    with 8+4-2-1=9 singular fibers. The altogether 9+3=12 points blown up from a minimal ruled rational surface Y=X3min->P1
    have to lie is special position. They satisfy conditions of expected codimension h^0(H)*h^1(H)=10 in the Hilbert scheme
    of 12 points on Y. Thus up to projectivities we expect a (24-6-10=8)-dimensional family of such surface.
   Example
    "betti(N=Hom(X,P4^1/X))";
    "HH^0(sheaf N) == kk^(8+24)";
   Text
     Another count: Up to projectivities and base changes the presentation matrix of the
     H^1-module of the ideal sheaf of X depends on (5+1+2)-4 parameters and the choice of the
     Hilbert-Burch homomorphism on dim G(2,4)=4 further parameters.
     This gives the same number 8 of parameters up to projectivities.
*-     

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
 enriquesSurfaceD11S10
 (enriquesSurfaceD11S10, PolynomialRing)
Headline
 get an Enriques surface of degree 11 and sectional genus 10 
Usage
 X= enriquesSurfaceD11S10 P4
Inputs
 P4:PolynomialRing
  coordinate ring of P4 over the field ZZ/3
Outputs
 X:Ideal
  of an Enriques surface of degree 11 in P4
Description
  Text
    One family of the surface found as "schreyerSurface"  is actually
    an Enriques surface. An example is the first surface in the list of precomputed
    schreyer surfaces.
  Example
    kk=ZZ/3;
    P4=kk[x_0..x_4];
    minimalBetti(X=enriquesSurfaceD11S10(P4))
    betti(T=tateResolutionOfSurface X)
    (d,sg)=(degree X, sectionalGenus X)
    LeBarzN6(d,sg,1)==10
    Ksquare(d,sg,1)==-6
    X5=ideal (gens X)_{0..4};
    R=X5:X;
    dim R,degree R,degree(R+X)
  Text
    There are 5 six-secant lines, hence by Le Barz formula five (-1) lines. Indeed:
  Example
    "elapsedTime (numList,L1,L2,Y)=adjunctionProcess(X,4); -- 48.7283s elapsed;";
    "numList=={(4, 11, 10), 5, (9, 19, 11), 1, (10, 20, 11), 0, (10, 20, 11), 0, (10, 20, 11)}";
    B=new BettiTally from {(0,{0},0) => 1, (1,{2},2) => 25, (2,{3},3) => 80,
      (2,{4},4) => 10, (3,{4},4) => 80, (3,{5},5) => 112, (4,{6},6) => 350,
      (5,{7},7) => 400, (6,{8},8) => 245, (7,{9},9) => 80, (8,{10},10) => 11}
    "degree Y==20";
    "minimalBetti Y == B";
    "2*sectionalGenus Y- 2== degree Y";
  Text
    The first adjunction maps blows down 5 (-1) lines. The second a (-1) conic.
    The second adjoint surface X2 is a minimal Enriques surface of degree 20
    in a P10.    
SeeAlso
    specialEnriquesSchreyerSurface
    specificSchreyerSurface
    adjunctionProcessData
    tateResolutionOfSurface
    LeBarzN6
    Ksquare
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
    (L0,adjList,ptsList, J)=adjunctionProcess X;
    betti(T=tateResolutionOfSurface X)
  Text
    Lebarz formula computes the number of 6-secant lines + the number of (-1) lines.
  Example 
    LeBarzN6(degree X, sectionalGenus X,1)
    X5=ideal (gens X)_{0..14};
    L=X5:X -- L is the six secant line
    degree(L+X)==6
  Text
    We can obtain information about this surface
    from the adjunctionProcess.
  Example 
    (L0,adjList,ptsList,J)=adjunctionProcess(X);
    ring J
    betti(H=parametrization(ring J,adjList))
    cH=primaryDecomposition ideal H;
    tally apply(cH,c->(dim c, degree radical c, degree c))
  Text
    H is a linear system of forms of degree which vanish in 10 points with
    multiplicity 4. However over the field the 10 point spit into orbits
    under Frobenius.
    In the second version of the function we start with
    a rational P2 - -> P4 defined by forms
    of degree 13 which vanishes on 10 randomly choosen
    points with multiplicity 4.
  Example
    P2=kk[y_0..y_2];
    elapsedTime minimalBetti(X=nonspecialAlexanderSurface(P4,P2))
    (L0,adjList,ptsList,J)=adjunctionProcess(X);
    betti(H=parametrization(ring J,adjList))
    cH=primaryDecomposition ideal H;
    tally apply(cH,c->(dim c, degree radical c, degree c))
  Text
    This times the ideal H decomposes in to 10 points of degree 1 defined ove kk
    and an embedded (y_0..y_2)-primary ideal. 
SeeAlso
   enriquesSurfaceOfDegree9
   tateResolutionOfSurface
   LeBarzN6
   adjunctionProcess
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
 construct a Popescu surface (4 families)
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
 vBELSurface
 (vBELSurface, PolynomialRing)
 (vBELSurface, Ring,Ring)
Headline
 construct a von Bothmer-Erdenberger-Ludwig surface 
Usage
 X= vBElSurface(P4,P2)
 X= vBELSurface(P4) 
Inputs
 P4:PolynomialRing
  coordinate ring of P4
 P2:PolynomialRing
  coordinate ring of P2
Outputs
 X:Ideal
  of a vBEL surface in P4
Description
  Text
   The first version gives the oringinal vBEL surface defined over a field of characteristic 2.
   The second version gives gives a construction of a vBEL surface building on a unirational liaison
   construction.
  Example
   P4=ZZ/2[x_0..x_4]; P2=ZZ/2[u_0..u_2];
   minimalBetti(X=vBELSurface(P4,P2))
   ci=ideal ((gens X)_{0}|(gens X)*random(source gens X,P4^{-5}));
   Y=ci:X;
   setRandomSeed("fast decomposition")
   cY=decompose Y;
   tally apply(cY, c-> (dim c, degree c, minimalBetti c))
   betti(T=tateResolutionOfSurface X)
  Text
   The linked surface consists of a plane, a quadric surface and a Bordiga surface.
   The unirational construction is a reversal of this linkage.
  Example
   kk=ZZ/nextPrime 10^3; P4=kk[x_0..x_4];
   minimalBetti(X=vBELSurface P4)
   betti tateResolutionOfSurface X
   (L0,L1,L2,J)=adjunctionProcess(X);
   L0
   X45=ideal (gens X)_{0..5};
   R=X45:X;
   dim R, degree R
   cR=decompose R;
   tally apply(cR,c->(dim c, degree c, betti c))
   tally apply(cR,c->degree(c+X))
   LeBarzN6(11,11,1)
  Text
   X has two 6-secant lines and five (-1)-lines.
SeeAlso
  adjunctionProcessData

///

///
-- the (4,5) linked surface of a vBEL surface can be irreducible:
   kk=ZZ/nextPrime 10^3; P4=kk[x_0..x_4];
   minimalBetti(X=vBELSurface P4)
   singX=saturate(X+minors(2,jacobian X));
   dim singX
   betti (T=tateResolutionOfSurface X)
   betti(T.dd_4)_{3}
   ci=ideal ((gens X)_{0}|(gens X)*random(source gens X,P4^{-5}));
   Y=ci:X;
   --setRandomSeed("fast decomposition")
   elapsedTime cY=decompose Y;-- 328.197 seconds elapsed
   tally apply(cY, c-> (dim c, degree c, minimalBetti c))  
   singY=saturate(Y+minors(2,jacobian Y));
   minimalBetti singY
   dim singY, degree singY
   csingY=primaryDecomposition singY;
   tally apply(csingY,c->(dim c, degree c, minimalBetti c))
   betti(omegaY=Ext^1(module Y,P4^{-5}))
   betti (m4xx=syz (m6x13=presentation omegaY)^{4,5})
   betti(m4xr=m6x13^{0..3}*m4xx)
   minimalBetti coker m4xr
   P3=kk[y_0..y_3]
P3xP4=P3**P4
betti(graph=ideal(sub(vars P3,P3xP4)*sub(m4xr,P3xP4)))
betti (sg=saturate(graph,sub(ideal gens P4,P3xP4)))
minimalBetti(inP3=trim sub(sg,P3))
cinP3=decompose(inP3)
tally apply(cinP3,c->(dim c, degree c))
quadric=first cinP3
while(
    line=ideal random(P3^1,P3^{2:-1});
    pts=decompose (line + quadric);
    #pts<2) do ()
pt=sub(transpose syz transpose jacobian first pts,kk)
fib=trim ideal(pt*m4xr)
fib0=trim ideal(random(kk^1,kk^4)*m4xr)
m4x4=m4xr_{0..3}
 ann coker m4x4==ideal Y_0
singY0=saturate ideal jacobian Y_0;
dim singY0, degree singY0
apply(decompose  singY0,c->(dim c, degree c, minimalBetti c))
line1=(decompose singY0)_1
line=(decompose singY0)_0
betti (H=intersect(line,line1))
cH=primaryDecomposition saturate(Y+ideal H_0);
tally apply(cH,c->(dim c, degree c , minimalBetti c, minimalBetti radical c, genus c))
degree(line+X)
apply(5,i->(dim(line^i+Y),degree(line^i+Y)))
degree Y,sectionalGenus Y
intersect
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


doc ///
Key
 quinticEllipticScroll
 (quinticEllipticScroll, PolynomialRing)
Headline
 construct a quintic elliptic scroll 
Usage
 X=quinticEllipticScroll P4
Inputs
 P4:PolynomialRing
  coordinate ring of P4
Outputs
 X:Ideal
  of a quintic elliptic scroll
Description
  Text
   We construct an quintic elliptic scroll, which is a nonsingular surface of
   degree 5 and sectional genus 1. It is linked via two cubics to the Veronese surface
   of degree 4.
  Example
   kk=ZZ/nextPrime 10^3;
   P4=kk[x_0..x_4];
   X=quinticEllipticScroll P4;
   (d,sg)=(degree X, sectionalGenus X)
   minimalBetti X
   betti(T=tateResolutionOfSurface X)
   ci=ideal(gens X* random(source gens X,P4^{2:-3}));
   Y=ci:X; -- Y is a Veronese surface
   minimalBetti Y
   (degree Y, sectionalGenus Y)==(4,0) 
SeeAlso
  veroneseSurface
  tateResolutionOfSurface
///

doc ///
Key
 ellipticConicBundle
 (ellipticConicBundle, PolynomialRing)
Headline
 construct a elliptic conic bundle 
Usage
 X=ellipticConicBundle P4
Inputs
 P4:PolynomialRing
  coordinate ring of P4
Outputs
 X:Ideal
  of a elliptic conic bundle
Description
  Text
   We construct an elliptic conic bundle, which is a nonsingular surface of
   degree 8 and sectional genus 5.
  Example
   kk=ZZ/nextPrime 10^3;
   P4=kk[x_0..x_4];
   X=ellipticConicBundle P4;
   (d,sg)=(degree X, sectionalGenus X)
   minimalBetti X
   betti(T=tateResolutionOfSurface X)
 Text
  These surface where overlooked by Okonek and Ionescu respectively in their classification of low
  degree smooth projective surfaces.
References
  Okonek
  Iounescu
  Abo et al
SeeAlso
  tateResolutionOfSurface
///

doc ///
Key
 biellipticSurfaceD10
 (biellipticSurfaceD10,PolynomialRing)
Headline
 construct a bielliptic surface of degree 10 
Usage
 X=biellipticSurfaceD10 P4
Inputs
 P4:PolynomialRing
  coordinate ring of P4
Outputs
 X:Ideal
  of a bielliptic surface of degree 10 
Description
  Text
  Example
   kk=ZZ/nextPrime 10^3;
   P4=kk[x_0..x_4];
   elapsedTime X=biellipticSurfaceD10 P4;
   (d,sg)=(degree X, sectionalGenus X)
   minimalBetti X
   betti(T=tateResolutionOfSurface X)
 Text
   The construction uses Moore matrices and a search for 6 torsions point on an elliptic curve .
   Perhaps the code can be improved.
References
  ADHPR
SeeAlso
  tateResolutionOfSurface
///

doc ///
Key
 biellipticSurfaceD15
 (biellipticSurfaceD15,PolynomialRing)
Headline
 construct a bielliptic surface of degree 15 
Usage
 X=biellipticSurfaceD10 P4
Inputs
 P4:PolynomialRing
  coordinate ring of P4
Outputs
 X:Ideal
  of a bielliptic surface of degree 10 
Description
  Text
  Example
   kk=ZZ/nextPrime 10^4; 
   P4=kk[x_0..x_4];
   elapsedTime X=biellipticSurfaceD15 P4;
   (d,sg)=(degree X, sectionalGenus X)
   minimalBetti X
   betti(T=tateResolutionOfSurface X)
 Text
   The construction uses Moore matrices and a search for 6 torsions point on an elliptic curve .
   Perhaps the code can be improved.
Caveat
   The function can fail, in which case it returns null.
References
  ADHPR
SeeAlso
  tateResolutionOfSurface
///

doc ///
Key
 abelianSurfaceD10
 horrocksMumfordSurface 
 (horrocksMumfordSurface,PolynomialRing)
 (abelianSurfaceD10,PolynomialRing)
Headline
 construct a nonsingular abelian surface of degree 10 and sectional genus 6 
Usage
 X=abelianSurfaceD10 P4
 X=horrocksMumfordSurface P4
Inputs
 P4:PolynomialRing
  coordinate ring of P4
Outputs
 X:Ideal
  of a abelian surface of degree 10, a Horrocks-Mumford surface. 
Description
  Text
   Horrocks and Mumford rediscovered these surfaces as the zero locus of sections of the
   Horrocks-Mumford bundle, which is a rank 2 vector bundle with
   Chern classes c1=-1 and c2=4.
   Commesati found these surface already in 192x?.
  Example
   kk=ZZ/nextPrime 10^4; 
   P4=kk[x_0..x_4];
   X=abelianSurfaceD10 P4;
   (d,sg)=(degree X, sectionalGenus X)
   betti(fX=res X)
   betti(T=tateResolutionOfSurface X)
 Text
   The surface X is the zero loci of a vector bundle, whose
   module of global sections is
 Example
  HMBundle=coker transpose (syz transpose fX.dd_3)_{0..18};
  minimalBetti HMBundle
 Text
  In the code we use the Horrocks-Mumford bundle get X. 
  The constuction of the Horrocks-Mumford bundle uses a monad:
 Example
  e=symbol e;
  E=kk[e_0..e_4,SkewCommutative=>true]; 
  alphad= map(E^{5:0},E^{2:-2},{{e_4*e_1,e_2*e_3},{e_0*e_2,e_3*e_4},{e_1*e_3,e_4*e_0},{e_2*e_4,e_0*e_1},{e_3*e_0,e_1*e_2}});
 Text
  The matrix
 Example
  diagonalMatrix{1,-1}*transpose alphad
 Text
  is the famous Horrocks-Mumford matrix which leads to a Tate resolution of the following shape
 Example
  betti (F=res coker alphad);
  betti (F'=res(coker transpose F.dd_6,LengthLimit=>9)[5])
 Text
  The Horrocks-Bundle is obtained as the homology of a monad. The module HMbundle below
  is the module of global sections of the Horrocks-Mumford bundle.
 Example
  HMbundle= prune homology(beilinson(F'.dd_0**E^{-4},P4),beilinson(F'.dd_1**E^{-4},P4))
  minimalBetti HMbundle
  minimalBetti X
 Text
  The Hilbert function of the cohomology of the Horrocks-Mumford bundle is incoded in the
  Tate resolution, cf. [EFS,pp xxx].
 Example
  H2cohomology=prune Ext^2(HMbundle,P4^{-5})
  H1cohomology=prune Ext^1(HMbundle,P4^{-5})
  apply(toList(3..8),i->hilbertFunction(i,H1cohomology))
  betti F'
References
  Horrocks-Mumford
  Barth-Hulek-Moore
  Comessati
  Decker-Schreyer
  Eisenbud-Floystad-Schreyer
SeeAlso
///

doc ///
Key
 abelianSurfaceD15
 (abelianSurfaceD15, PolynomialRing)
Headline
 construct an abelian surface of degree 15
Usage
 X=abelianSurfaceD15 P4
Inputs
 P4:PolynomialRing
  coordinate ring of P4
Outputs
 X:Ideal
  of an abelian surface of degree 15
Description
  Text
   These abelian surfaces are linked via two quintics to a Horrocks-Mumford surface.
   The construction uses this liason
  Example
   kk=ZZ/nextPrime 10^3;
   P4=kk[x_0..x_4];
   X=abelianSurfaceD15 P4;
   (d,sg)=(degree X, sectionalGenus X)
   minimalBetti X
   ci=ideal(gens X* random(source gens X,P4^{2:-5}));
   Y=ci:X;
  Text
   Y is a Horrocks-Mumford surface.
  Example
   minimalBetti Y
   (degree Y, sectionalGenus Y) == (10,6)
  Text
   The surface is non-mimimal. Adjunction gives
  Example
   betti (HplusK=presentation truncate(1,Ext^1(X,P4^{-5})))
   P19=kk[y_0..y_19];
   P4xP19=P4**P19;
   graph=sub(vars P19,P4xP19)*sub(HplusK,P4xP19);
   betti(presH=map(P19^5,,sub(contract(transpose sub(vars P4,P4xP19),graph),P19)))
   --elapsedTime betti(X1=ann coker presH)
  Text
   X1 is the first adjoint surface.

References
   Horrocks-Mumford
   BHM
   
SeeAlso
  horrocksMumfordSurface
  adjunctionProcessData
///
-*
  Example
   (dim X1,degree X1,sectionalGenus X1)==(3,40,21)
  Text
   The image H1 of a general hyperplane section of X under the adjunction map is a
   canonical curve, however projected since h^2(\omega_X)=1.
  Example
   elapsedTime H1=ann coker(random(P19^4,P19^5)*presH)
   betti H1
   (dim H1, degree H1, genus H1)==(2,40,21)
   elapsedTime pts=sum apply(3,i->ann coker(random(P19^4,P19^5)*presH));
   (dim pts, degree pts)==(1,25)
  Text
   the ideal pts is the ideal of the intersection the of three general hypersurface.
   Thus this ideal defines the exceptional points of the first adjunction map X -> X1.
   Indeed their preimage coincides with the 25 Horrocks-Mumford lines, see [HM]
   The structure sheaf of OX has Euler characteristic O and K^2=-25
  Example
   OX=sheaf(P4^1/X);
   apply(3,i->HH^i(OX))
   Ksquare(degree X, sectionalGenus X, 0)==-25
  Text
   Thus the surface X1 is minimal.
*-




doc ///
Key
 regularEllipticSurfaceD12
 (regularEllipticSurfaceD12,PolynomialRing)
Headline
 construct a regular elliptic surface of degree 12 
Usage
 X=regularEllipticSurfaceD12 P4
Inputs
 P4:PolynomialRing
  coordinate ring of P4
Outputs
 X:Ideal
  of a regular elliptic surface of degree 12 
Description
  Text
   We construct a regular elliptic surface of degree 12 and pg=2.
  Example
   kk=ZZ/nextPrime 10^4; 
   P4=kk[x_0..x_4]; 
   X=regularEllipticSurfaceD12 P4;
   (d,sg)=(degree X, sectionalGenus X)
   minimalBetti X
   betti(T=tateResolutionOfSurface X)
   OX=sheaf(P4^1/X);
   apply(3,i->HH^i(OX))
   Ksquare(degree X,sectionalGenus X,3)
 Text
   Since K^2=0 this surface is minimal.   
References
  
SeeAlso
  tateResolutionOfSurface
///

doc ///
Key
 irregularEllipticSurfaceD12
 (irregularEllipticSurfaceD12,PolynomialRing)
Headline
 construct a regular elliptic surface of degree 12 
Usage
 X=irregularEllipticSurfaceD12 P4
Inputs
 P4:PolynomialRing
  coordinate ring of P4
Outputs
 X:Ideal
  of a irregular elliptic surface of degree 12 
Description
  Text
   We construct a irregular elliptic surface of degree 12 and pg=2.
  Example
   kk=ZZ/nextPrime 10^4; 
   P4=kk[x_0..x_4]; 
   X=irregularEllipticSurfaceD12 P4;
   (d,sg)=(degree X, sectionalGenus X)
   minimalBetti X
   OX=sheaf(P4^1/X);
   apply(3,i->HH^i(OX))
   Ksquare(degree X,sectionalGenus X,3)
   --betti (T=tateResolutionOfSurface X) -- there is a bug in TateReolutionOfSurface
 Text
   Since K^2=0 this surface is minimal.   
References
  
SeeAlso
  tateResolutionOfSurface
///

doc ///
Key
 K3surfaceD7
 (K3surfaceD7, PolynomialRing)
Headline
 construct a K3 surface of degree 7
Usage
 X=K3surfaceD7 P4
Inputs
 P4:PolynomialRing
  coordinate ring of P4
Outputs
 X:Ideal
  of a elliptic conic bundle
Description
  Text
   We construct an K3 surface of degree 7 and sectional genus 5.
  Example
   kk=ZZ/nextPrime 10^3;
   P4=kk[x_0..x_4];
   X=K3surfaceD7 P4;
   (d,sg)=(degree X, sectionalGenus X)
   minimalBetti X
   OX=sheaf(P4^1/X);
   apply(3,i->HH^i(OX))
   Ksquare(degree X,sectionalGenus X,2)
   LeBarzN6(7,5,2)
  Text
   X is nonminimal with one exceptional line.
References
  Okonek
  Iounescu

SeeAlso
  
///

doc ///
Key
 K3surfaceD8
 (K3surfaceD8, PolynomialRing)
Headline
 construct a K3 surface of degree 8
Usage
 X=K3surfaceD8 P4
Inputs
 P4:PolynomialRing
  coordinate ring of P4
Outputs
 X:Ideal
  of a K3 surface of degree 8
Description
  Text
   We construct an K3 surface of degree 8 and sectional genus 6.
  Example
   kk=ZZ/nextPrime 10^3;
   P4=kk[x_0..x_4];
   X=K3surfaceD8 P4;
   (d,sg)=(degree X, sectionalGenus X)
   minimalBetti X
   OX=sheaf(P4^1/X);
   apply(3,i->HH^i(OX))
   Ksquare(degree X,sectionalGenus X,2)
   LeBarzN6(8,6,2)
   HdotK(8,6)
  Text
   X is non-minimal with one exceptional curve of degree 2.
References
  Okonek
  Iounescu

SeeAlso
  
///


doc ///
Key
 K3surfaceD9
 (K3surfaceD9, PolynomialRing)
Headline
 construct a K3 surface of degree 8
Usage
 X=K3surfaceD9 P4
Inputs
 P4:PolynomialRing
  coordinate ring of P4
Outputs
 X:Ideal
  of a K3 surface of degree 9
Description
  Text
   We construct an K3 surface of degree 9 and sectional genus 8.
  Example
   kk=ZZ/nextPrime 10^3;
   P4=kk[x_0..x_4];
   X=K3surfaceD9 P4;
   (d,sg)=(degree X, sectionalGenus X)
   minimalBetti X
   OX=sheaf(P4^1/X);
   apply(3,i->HH^i(OX))
   Ksquare(degree X,sectionalGenus X,2)
   LeBarzN6(9,8,2)
   HdotK(9,8)==5
  Text
   X is non-minimal with five exceptional lines.
References
  Okonek
  Iounescu

SeeAlso
  
///


doc ///
Key
 K3surfaceD10S9SL1
 (K3surfaceD10S9SL1, PolynomialRing)
Headline
 construct a K3 surface of degree 10 and sectional genus 9 with 1 six-secant line
Usage
 X=K3surfaceD10S9SL1 P4
Inputs
 P4:PolynomialRing
  coordinate ring of P4
Outputs
 X:Ideal
  of a K3 surface of degree 9
Description
  Text
   We construct an K3 surface of degree 10 and sectional genus 9 with one 6-secant line
  Example
   kk=ZZ/nextPrime 10^3;
   P4=kk[x_0..x_4];
   X=K3surfaceD10S9SL1 P4;
   (d,sg)=(degree X, sectionalGenus X)
   minimalBetti X
   OX=sheaf(P4^1/X);
   apply(3,i->HH^i(OX))
   Ksquare(degree X,sectionalGenus X,2)
   LeBarzN6(10,9,2)
   HdotK(10,9)
  Text
   X is non-minimal with two exceptional lines and three exceptional conics.
References
  Okonek
  Iounescu

SeeAlso
  
///

doc ///
Key
 K3surfaceD10S9SL3
 (K3surfaceD10S9SL3, PolynomialRing)
Headline
 construct a K3 surface of degree 10 and sectional genus 9 with 3 six-secant line
Usage
 X=K3surfaceD10S9SL3 P4
Inputs
 P4:PolynomialRing
  coordinate ring of P4
Outputs
 X:Ideal
  of a K3 surface of degree 9
Description
  Text
   We construct an K3 surface of degree 10 and sectional genus 9
  Example
   kk=ZZ/nextPrime 10^3;
   P4=kk[x_0..x_4];
   X=K3surfaceD10S9SL3 P4;
   (d,sg)=(degree X, sectionalGenus X)
   minimalBetti X
   OX=sheaf(P4^1/X);
   apply(3,i->HH^i(OX))
   Ksquare(degree X,sectionalGenus X,2)
   LeBarzN6(10,9,2)
   HdotK(10,9)
  Text
   X is non-minimal with no exceptional line and three exceptional conics.
   The three 6-secant lines arize as follows:
  Example
   betti(X5=ideal (gens X)_{0..5})
   betti(plane=X5:X)
   dim plane == 3
   dim  (plane+X), degree radical (plane+X)
   tally apply(primaryDecomposition (plane+X),c->(dim c, degree radical c))
  Text
   The plane intersects X in a quartic curve and three points. The three lines through
   two of these points are the thee 6-secant lines.

  
References

SeeAlso
  
///

doc ///
Key
 K3surfaceD11S11SLn
 (K3surfaceD11S11SLn, PolynomialRing,ZZ)
Headline
 construct a K3 surface of degree 11, sectional genus 11 and precisely n six-secants lines
Usage
 X=K3surfaceD11S11SLn(P4,n)
Inputs
 P4:PolynomialRing
  coordinate ring of P4
 n: ZZ
   the number of desired six secant lines
Outputs
 X:Ideal
  of a K3 surface of degree 11, sectional genus 11 and precisely 'n' six-secants lines
Description
  Text
   We construct an K3 surfaces of degree 11, sectional genus 11 and n six-secants lines
  Example
   kk=ZZ/nextPrime 10^3;
   P4=kk[x_0..x_4];
   X=K3surfaceD11S11SLn(P4,0);
   (d,sg)=(degree X, sectionalGenus X)
   minimalBetti X
   --OX=sheaf(P4^1/X);
   --apply(3,i->HH^i(OX))
  Text
   X has no 6-secant line, since the ideal is generated by quintics.
  Example
   X=K3surfaceD11S11SLn(P4,1);
   minimalBetti X
  Text
   In case n=1 there is precisely one 6-secant line:
  Example
   betti(X5=ideal (gens X)_{0..8})
   betti(line=X5:X)
   dim line, degree line, degree (line+X)
  Text
   In case n=2 there are 2 six secant lines:
  Example
   X=K3surfaceD11S11SLn(P4,2);
   minimalBetti X
   betti(X5=ideal (gens X)_{0..8})
   betti(residual=X5:X)
   dim residual, degree residual, degree (residual+X)
  Text
   In case n=3 there are 3 six secant lines:
  Example
   X=K3surfaceD11S11SLn(P4,3);
   minimalBetti X
   betti(X5=ideal (gens X)_{0..8})
   betti(plane=X5:X)
   dim plane, degree (plane+X)
   tally apply(primaryDecomposition(plane+X),c->(dim c, degree radical(c+X)))
  Text
   So the plane intersects X in a plane quartic and 3 points.
   The three 6-secant lines are the lines in the plane joining 2 of the three points.
  Example
   Ksquare(11,11,2)
   LeBarzN6(11,11,2)
   HdotK(11,11)
  Text
   Summary: X is a K3 surface with precisely e1=(4-n) exceptional lines and further exceptional curves
   of larger degree as in the following pattern (e1,e2,e3,..)
   (4,0,0,0,1), (3,0,2), (2,2,1), (1,4)
References
  Popescu
  
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


P4=ZZ/nextPrime 10^3[x_0..x_4]
m2x3=random(P4^{0,-1},P4^{3:-2});
X=minors(2,m2x3)
minimalBetti X, degree X, sectionalGenus X
singX=saturate(X+minors(2,jacobian X))
(L0,L1,L2,J)=adjunctionProcess(X);
L0
minimalBetti J
LeBarzN6(7,5,2)
betti(omegaX=Ext^1(module X,P4^{-5}))

chiITable(12,13)
chiI(6,12,13)
 chiITable(13,15)
 chiI(6,13,15)
 LeBarzN6(13,15,1)
 Ksquare(13,15,1)
d=13,sg=15
 chiITable(d,sg)
apply(toList(-5..7),i-> chiI(i,d,sg))
 LeBarzN6(d,sg,1)
 Ksquare(d,sg,1)

kk=ZZ/5
E=kk[e_0..e_4,SkewCommutative=>true]
E2=basis(2,E)
E3=basis(3,E)
m5x3=matrix apply(5,i-> apply(3,j->E_((i+j)%5)+E_((i-j)%5))
)
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
betti res coker (m2x5**E^{1}||Ar)
betti res coker transpose (m2x5**E^{1}||Ar)
