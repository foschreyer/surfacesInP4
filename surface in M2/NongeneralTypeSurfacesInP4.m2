///
restart

uninstallPackage "NongeneralTypeSurfacesInP4"
restart
loadPackage ("NongeneralTypeSurfacesInP4",Reload=>true)
installPackage "NongeneralTypeSurfacesInP4"

viewHelp "NongeneralTypeSurfacesInP4"
check "NongeneralTypeSurfaceInP4"
path
viewHelp 
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
    "aboRanestadSurfaces",
    "tateResolutionOfSurface",
    "outputOfTheAdjunctionProcessCommand"
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

-* Documentation section *-


beginDocumentation()


document {
Key => NongeneralTypeSurfacesInP4,
Headline => "Construction of smooth non-general type surfaces in P4",
   "In 1989 Elligsrud and Peskine proved a conjecture of Harstshorne and Lichtenbaum about smooth rational surfaces in P4 more general:
    There are only finitely many components of the Hilbert scheme of surfaces in P4, whose general point correspond to a smooth 
    surface not of general type.

   In that period there was a flurish of activities to construct such surfaces, in part using Computer Algebra. In this package we review
   those construction, which after 30 years of Macaulay2 have become simpler and faster. Moreover we have discovered a couple of further 
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
	TO unirationalFamilies,
	TO constructionsViaFiniteFieldSearches,
	TO extensionToCharacteristicZero,
	TO LabBookProtocol
        }     
}


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
    The smooth cubic scroll in is uniquely determined up to projectivities.
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
    We compute the image from the parametization.
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
    We construct a Castelnuove surface from its Hilbert-Burch matrix
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
  of the cubic scroll in P4
Description
  Text
    We construct the surface from a carefully choosen H^1_*(I_X) module of the ideal sheaf I_X
    with Hilbert function (2,5,3).
  Example
    kk=ZZ/nextPrime 10^3;
    P4=kk[x_0..x_4];
    minimalBetti(X=degree10pi8RanestadSurface P4)
    betti(T=tateResolutionOfSurface X)
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
  of a a nonspecial Alexander surface of degree 9 in P4
Description
  Text
    We construct a nonspecial Alexander surface of degree 9 from its rational parametrization,
    or what is faster from a presentation of the H^1_*(I_X) module. The dual of the (3,5,1) module has
    a special presentation which gives rize to a six sectant line
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
  of a a nonspecial Alexander surface of degree 9 in P4
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
  outputOfTheAdjunctionProcessCommand

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
    The last command should not be executed since it take too much time.

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

 




-- Leftover from popesuSurface
doc ///
Key
 popescuSurface
 (popescuSurface, PolynomialRing,Ring,Number)
Headline
 construct a Popescu surface 
Usage
 X= popescuSurface(P4,E,0)
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
    The Popescu surfaces come in three families, distinguished by their number of 6-secant lines.
    One has to choose the differential T.dd_4 suitable.
    In the first case X has no 6-secant, since the ideal is generated by quintics.
    In the second there is a unique 6-secant line.
    In the third case there is a pencil of 6-secant line. Every line in the plane through the point is a 6-secant line, since the plane intersects the surface in a plane quintic curve.
    Note that since the number of (-1) lines is larger than the quantity computed by Le Barz formula, there cannot be only finitely many 6-secants. 
  Example
    kk=ZZ/nextPrime 10^3;
    P4=kk[x_0..x_4];
    E=kk[e_0..e_4,SkewCommutative=>true];
    minimalBetti(X=popescuSurface(P4,E,0))
    (d,sg)=(degree X, sectionalGenus X) 
    betti(T=tateResolutionOfSurface X)
    
    elapsedTime minimalBetti(X=popescuSurface(P4,E,1))
    X5=ideal (gens X)_{0..9};
    L=X5:X, degree(L+X)
    elapsedTime (numList,L1,L2,J)=adjunctionProcess(X,1);
    numList_1
  Text
    The entry numList_1 is the number of (-1) lines on X. Thus we must have
  Example
    LeBarzN6(d,sg,1)==6+1
    elapsedTime minimalBetti(X=popescuSurface(P4,E,2))
    X5=ideal (gens X)_{0..9};
    R=X5:X 
    tally apply(primaryDecomposition (R+X),c->(dim c,degree radical c,degree(c+R)))
    elapsedTime (numList,L1,L2,J)=adjunctionProcess(X,1);
    numList_1 > LeBarzN6(d,sg,1)
 
    
SeeAlso
  outputOfTheAdjunctionProcessCommand

///




  Text
    So there is one 6-secant line.
  Example
    elapsedTime (numList,L1,L2,J)=adjunctionProcess(X,1);
    numList_1
  Text
    The entry numList_1 is the number of (-1) lines on X. Thus we must have
  Example
    LeBarzN6(d,sg,1)==6+1
  Text
    Since the number of (-1) lines + the number of 6-secant lines is computed by Le Barz formula.
  Example
    elapsedTime (numList,L1,L2,J)=adjunctionProcess(X,1);
    numList_1 > LeBarzN6(d,sg,1)
  Text
    Since the number of (-1) lines is larger than the quantity computed by Le Barz formula, there cannot be only finitely many 6-secants.

  Example
    numList, minimalBetti J
    Ksquare(d,sg,1)==8-7-9-3
  Text
    In this case the last adjoint surface is a Castelnuovo surface in P4 which is a Hirzebruch surface
    blown up in 7 points. The adjunction process blows-down 9 (-1) lines and 3 (-1) conics.
    Thus altogether there are 9+3+7 points blown-up.

