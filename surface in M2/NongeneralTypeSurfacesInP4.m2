///
restart 
needsPackage"NongeneralTypeSurfacesInP4"

elapsedTime installPackage "NongeneralTypeSurfacesInP4"

viewHelp "NongeneralTypeSurfacesInP4"

check "NongeneralTypeSurfacesInP4"


uninstallPackage "NongeneralTypeSurfacesInP4"
restart
needsPackage ("NongeneralTypeSurfacesInP4")
elapsedTime installPackage("NongeneralTypeSurfacesInP4")    -- 47.3775s elapsed, about 20 seconds for the examples

///


newPackage(
    "NongeneralTypeSurfacesInP4",
    Version => "0.8",
    Date => "April 28, 2025",
    Headline => "Construction of smooth non-general type surfaces in P4",
    Authors => {
	        { Name => "Hirotachi Abo",Email => "abo@uidaho.edu", HomePage => "https://sites.google.com/view/hirotachiabo/home"},
	        { Name => "Kristian Ranestad", Email => "ranestad@math.uio.no", HomePage => "https://add"},
	        { Name => "Frank-Olaf Schreyer", Email => "schreyer@math.uni-sb.de", HomePage => "https://www.math.uni-sb.de/ag/schreyer"}},
    AuxiliaryFiles => false,
    DebuggingMode => true,
    PackageExports => {"BGG","AdjunctionForSurfaces","PrimaryDecomposition","Varieties","FastMinors"},
    Keywords => {"Algebraic Geometry"},
    HomePage =>  "todo",
    )

export {
    "varietyOfUnstablePlanes",
    "searchHMBundle",
    "tangentToMonad",
    "randomEllipticAboSurface",
    "numericalFunctions",
    "specificAboRanestadSurface",
    "specificEllipticAboSurfaceD12S13",
    "specificEllipticSurfaceD13S16",
    "specificAboSurface",
    "collectSpecialAboSurfaces",
    "randomSpecialAboSurface",
    "numericalTypeOfResidualInQuintics",
    "partitionOfCanonicalDivisorOfAboSurface",
    "adjointMatrices",
    "Equations",
    "SingX",
    "Count",
    "PrintConstructionData",
    "analyzeAboSurface",
    "collectAboSurfaces",
    "aboSurfaces",
    "randomAboSurface",
    "randomAboSurfaceWithLargeHomSpace",
    "randomAboSurfaceWithHomSpaceOfGivenDimension",
    "aboSurfaceFromMatrix",
    "testMatrix",
    "testMatrix1",
    "testMatrix2",
    "WithM3x13",
    "WithX",
    "abo112224Or111234Surface",
    "abo111333Surface",
    "abo111117Surface",
    "abo111144Surface",
    "symExtFunction",
    "sectionalGenus",
    "chiO",
    "irregularity",
    "geometricGenus",
    "chiNX",
    "chiI",
    "chiITable",
    "HdotK",
    "Ksquare",
    "LeBarzN6",
    "residualInQuintics",
    "canonicalDivisor",
    "selfIntersectionNumber",
    "cubicScroll",
    "veroneseSurface",
    "delPezzoSurface",
    "castelnuovoSurface",
    "bordigaSurface",
    "ionescuOkonekSurfaceD7",
    "ionescuOkonekSurfaceD8S5",
    "okonekSurfaceD8S6",
    "nonspecialAlexanderSurface",
    "specialityOneAlexanderSurface",
    "degree10pi8RanestadSurface",
    "degree10pi9RanestadSurface",
    "degree10DESSurface",
    "popescuSurface",
    "enriquesSurfaceOfDegree9",
    "enriquesSurfaceOfDegree10",
    "enriquesSurfaceD11S10",
    "horrocksMumfordSurface",
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
    "findRandomSmoothSchreyerSurface",
    "collectSchreyerSurfaces",
    "tangentDimension",
    "schreyerSurfaceWith2LinearSyzygies",
    "schreyerSurfaceWith2or3LinearSyzygies",
    "unirationalConstructionOfSchreyerSurface",
    "specialEnriquesSchreyerSurface",
    "adjunctionProcessData",
    "prepareAboRanestadSurfaces",
    "aboRanestadSurface",
    "collectSmoothAboRanestadSurfaces",
    "aboRanestadSurfaceFromMatrix",
    "matrixFromAboRanestadSurface",
    "get4x2Matrix",
    "Smooth",
    "Special",
    "NumberOfRank1Points",
    "veroneseImagesInG25",
    "vBELSurface",
    "quinticEllipticScroll",
    "ellipticConicBundle",
    "irregularEllipticSurfaceD12",
    "ellipticSurfaceD12S13",
    "biellipticSurfaceD10",
    "biellipticSurfaceD15",
    "abelianSurfaceD10",
    "abelianSurfaceD15",
    "abelianSurfaceD15S21Popescu",
    "K3surfaceD6",
    "K3surfaceD7",
    "K3surfaceD8",
    "K3surfaceD9",
    "K3surfaceD10S9L1",
    "K3surfaceD10S9L3",
    "H1module",
    "K3surfaceD11S11Ln",
    "K3surfaceD11S12",
    "K3surfaceD12",
    "K3surfaceD13",
    "K3surfaceD14",
    "ellipticSurfaceD7",
    "ellipticSurfaceD8",
    "ellipticSurfaceD9",
    "ellipticSurfaceD10S9",
    "ellipticSurfaceD10S10",
    "ellipticSurfaceD11S12",
    "ellipticSurfaceD12S14L0",
    "ellipticSurfaceD12S14Linfinite",
    "K3surfaces",
    "surfacesOfKodairaDimension1",
}


-* Code section *-
-* numerical functions *-
sectionalGenus=method()
--  PURPOSE : Find the sectional genus of a variety
--    INPUT : 'X', the ideal of a variety
--   OUTPUT : an integer
--  COMMENT : The function uses the command 'genera'
sectionalGenus(Ideal):= X -> (genera X)_1

chiI=method()
--     PURPOSE : Find the Euler characteristic of the twisted sheaf I_X(m) on a surface 'X'
--      INPUTS : 'm',the number of twists
--               'd', the degree of 'X'
--               'sg', the sectional genus of the surface 'X'
--               'xO', the Euler characteristic of 'X' 
--      OUTPUT : an integer
-- DESCRIPTION : The function computes the difference between the dimensions of HH^0 OO_P4(m) and HH^0 OO_X(m)

chiI(ZZ,ZZ,ZZ,ZZ) := (m,d,sg,xO) -> binomial(m+4,4)-(binomial(m+1,2)*d-m*(sg-1)+xO)

chiO=method()
--      PURPOSE : Find the Euler characteristic of the structure sheaf on a variety 
--       INPUTS : 'X',the ideal of a variety
--       OUTPUT : an integer
--  DESCRIPTION : The function calculates the alternating sum of the dimensions of HH^i OO_X
--      COMMENT : The function uses 'HH'
chiO(Ideal) := X -> (
    Pn:= ring X;
    OX := sheaf(Pn^1/X);
    sum(toList(0..dim X),i-> (-1)^i*rank HH^i(OX))
    )

irregularity=method()
--      PURPOSE : Find the irregularity of a surface 
--        INPUT : 'X', the ideal of a surface
--       OUTPUT : an integer
--  DESCRIPTION : The function determines the irregularity by computing the dimension of HH^2(OO_X)
--      COMMENT : The function uses 'HH'
irregularity(Ideal) := X -> (
    if dim X !=3 then error "expected the ideal of a projective surface";
    Pn:= ring X;
    OX := sheaf(Pn^1/X);
    rank HH^1(OX))

geometricGenus=method()
--     PURPOSE : Find the geometric genus of a surface
--       INPUT : 'X',the ideal of a surface
--      OUTPUT : an integer
-- DESCRIPTION : The function makes the structure sheaf OO_X of the surface
--               and calculates the dimension of HH^2(OO_X)
geometricGenus(Ideal) := X -> (
    if dim X !=3 then error "expected the ideal of a projective surface";
    Pn:= ring X;
    OX := sheaf(Pn^1/X);
    rank HH^2(OX))

chiNX = method();
-- PURPOSE : Find the Euler characteristic of the normal bundle of a nonsingular surface 'X' in projective space 'P4'
--   INPUT : 'd', degree of 'X'
--           'Pi',sectional genus of 'X'
--           'Chi', euler characteristic of 'X' 
--  OUTPUT : Euler characteristic of the normal bundle of 'X' in 'P4'
-- COMMENT : The command can also take the ideal of 'X' and returns the Euler characteristic of the normal bundle of 'X' in 'P4'
chiNX(ZZ,ZZ,ZZ) := (d,Pi,Chi) -> (
    5*d-5*Pi-2*Ksquare(d,Pi,Chi)+14*Chi+5
    )
chiNX(Ideal) := X -> (
    assert(dim X-1 == 2);
    d := degree X;
    Pi := sectionalGenus X;
    Chi := genus X+1;
    chiNX(d,Pi,Chi)
    )
///    
chiNX(12,13,2)
///

chiITable=method()
--  PURPOSE : Find the Betti diagram of the Tate resolution of the ideal sheaf of a surface 'X',
--            provided that 'X' has natural cohomology
--   INPUTS : 'd', the degree of 'X'
--            'sg', the sectional genus of 'X'
--            'xO', the Euler characteristic of 'X'
--   OUTPUT : a Betti tally
--  COMMENT : The function uses 'BettiTally'
chiITable(ZZ,ZZ,ZZ) := (d,sg,xO) -> (
    -- 'L' is the list of the Euler characteristics of I_X(d), -4<=d<=8
    L:=apply(toList(-4..8),m->chiI(m,d,sg,xO));
    -- 'l' is the number of elements in 'L'
    l:=#L;
    -- 'h3' is the positin of the first positive integer on 'L'
    h3:=position(L,h->h>0);
    -- 'L3' is the list of integers from 'L'_0 to 'L'_{'h3'-1}
    L3:=L_{0..h3-1};
    -- 'h2' is the position of the first negative integer on 'L' after 'h3' 
    h2:=position(L_{h3..l-1},h->h<0);
    -- 'L2' is the list of integers from 'L'_{'h3'} to 'L'_{'h3'+'h2'-1}
    L2:=L_{h3..h3+h2-1};
    -- 'h1' is the position of the first positive integer on 'L' after 'h2' 
    h1:=position(L_{h3+h2..l-1},h->h>0);
    -- 'L1' is the list of integers from 'L'_{'h3'+'h2'} to 'L'_{'h3'+'h2'+'h1'-1}
    L1:=L_{h3+h2..h3+h2+h1-1};
    -- 'L0' is the list of the remaining integers
    L0:=L_{h3+h2+h1..l-1};
    -- 'Hi' is the list of tripes encoding columns, degrees, and rows together with the operation '=> L_i' 
    H3:=apply(#L3,i->(i-1,{-4+i},-4+i)=>-L3_i);
    H2:=apply(#L2,i->(i+h3-2,{-4+i+h3},-4+i+h3)=>L2_i);
    H1:=apply(#L1,i->(i+h3+h2-3,{-4+i+h3+h2},-4+i+h3+h2)=>-L1_i);
    H0:=apply(#L0,i->(i+h3+h2+h1-4,{-4+i+h3+h2+h1},-4+i+h3+h2+h1)=>L0_i);
    H4:={(-1,{-5},-5)=>1};
    -- Use 'BettiTally' to display the Betti diagram 
    new BettiTally from (H4|H3|H2|H1|H0))

/// -* Test chiTable *-
kk=ZZ/nextPrime 10^4
P4=kk[x_0..x_4]
E=kk[e_0..e_4,SkewCommutative=>true]
(X,m3x4)=abo111333Surface(P4,E);
B=betti tateResolutionOfSurface(X,7)

d=12,sg=13,xO=2
A=chiITable(d,sg,xO)
assert(A==B)

///


HdotK=method()
--  PURPOSE : Compute the intersection number of the hyperplane and canonical classes of a surface 'X' using the adjunction formula
--   INPUTS : 'd',the degree of 'X'
--            'sg', the sectional genus of 'X'
--   OUTPUT : an integer
HdotK(ZZ,ZZ) := (d,sg) -> 2*(sg-1)-d
   
Ksquare=method()
--  PURPOSE : Compute the self intersection number of the canonical classes of a surface 'X' using the double point formula
--   INPUTS : 'd',the degree of 'X'
--            'sg', the sectional genus of 'X'
--            'xO', the Euler characteristic of 'X'
--   OUTPUT : an integer
-- H2+HK=2(sg-1)
-- d^2-10d-5HK-2K2+12x==0
Ksquare(ZZ,ZZ,ZZ) := (d,sg,xO) -> (HK:=2*(sg-1)-d;
    floor(1/2*(d^2-10*d-5*HK+12*xO)))

LeBarzN6=method()
--  PURPOSE : Compute the sum of the numbers of 6-secant lines and (-1)-lines of a surface 'X' using Le Barz's formula
--   INPUTS : 'd',the degree of 'X'
--            'sg', the sectional genus of 'X'
--            'xO', the Euler characteristic of 'X'
--   OUTPUT : an integer
LeBarzN6(ZZ,ZZ,ZZ) := (d,sg,xO) -> (
    delta:=binomial(d-1,2)-sg;
    t:= binomial(d-1,3)-sg*(d-3)+2*(xO-1);
    h:= floor(1/2*(delta*(delta-d+2)-3*t));
    floor(-1/144*d*(d-4)*(d-5)*(d^3+30*d^2-577*d+786)+
	    delta*(2*binomial(d,4)+2*binomial(d,3)-45*binomial(d,2)+148*d-317)-
	    1/2*binomial(delta,2)*(d^2-27*d+120)-2*binomial(delta,3)+
	    h*(delta-8*d+56)+t*(9*d-3*delta-28)+binomial(t,2))
    )

residualInQuintics=method()
--  PURPOSE : Find the residual scheme to a surface in the variety cut out by the quintic hyersrfaces containing the surface 
--   INPUTS : 'X',the ideal of a surface
--   OUTPUT : an ideal 
residualInQuintics(Ideal) := X -> (
    -- 'pos' is the list of positions of the generators whose degrees are less than 6 
    pos := positions(flatten (degrees gens X)_1,d->d<6);
    -- 'X5' is the ideal generated by the generators of 'X' whose degree are less than 6
    X5 := ideal (gens X)_pos;
    -- Return the ideal quotient of 'X5' by 'X' 
    --residual:=
    X5:X)

canonicalDivisor=method()
-- PURPOSE : Find the ideal of a caninical divisor on a nonsingular surface in projective four-space 'P4'
--   INPUT : 'X', the ideal of a nonsingular surface in 'P4' with a positive geometric genus
--  OUTPUT : an ideal
canonicalDivisor(Ideal) := X -> (
    -- Check whether 'X' is a surface in P4
    if not (dim X==3 and codim X ==2) then
         error "expected the homogeneous ideal of a surface in P4";
    -- Compute the Tate resolution of 'X' and its Betti diagram
    B := betti tateResolutionOfSurface X;
    -- Compute the geometric genus of 'X'
    -- (Is it slower to calculate rank HH^2 OO_X?) 
    pg:= B#(3,{0},0);
    -- If 'pg' is zero, then return an error message
    if not pg >0 then error "expected a surface with geometric genus pg>0";
    P4 := ring X;
    -- 'OmegaX' is the canonical sheaf on 'X' 
    omegaX := presentation trim Ext^1(X,P4^{-5});
    -- Select a section of 'OmegaX' randomly
    rSect:= null;
    while ( -- avoid 0 section
    rSect=random(target omegaX, P4^{0});
    rSect==0) do ();
--    D:=ann coker (omegaX|rSect);
--    D
    ann coker (omegaX|rSect))




selfIntersectionNumber=method()
--     PURPOSE : Compute the self intersection number of a divisor on a surface in projective fourspace 'P4' using the adjunction formula
--      INPUTS : 'X', the ideal of a surface
--               'D', the ideal of an effective divisor on the surface 
--      OUTPUT : an integer
-- DESCRIPTION : The function computes '2D' and the genera 'g1' and 'g2' of 'D' and '2D', and it returns 'D'.'D' = 'g2'-1-(2'g1'-2) obtained by solving 2'g1'-2 ='D'.('D'+'K') and 2'g2'-2 = '2D'.('2D'+'K') for 'D'.'D'
selfIntersectionNumber(Ideal,Ideal) := (X,D) -> (
    -- Check whether 'X' is a surface in P4
    if not (dim X==3 and dim D == 2) then
         error "expected the ideal of an effective divisor on a surface";
    -- Find '2D'
    twoD := saturate(D^2+X);
    -- Compute the genera of 'D' and '2D' 
    g2 := genus twoD;
    g1 := genus D;
    g2-1-(2*g1-2))
///
kk=ZZ/nextPrime 10^4
P4=kk[x_0..x_4]
X=K3surfaceD8 P4;
minimalBetti X
D=canonicalDivisor X;
degree D
selfIntersectionNumber(X,D)
///

-- Symbols
--      Pn : projective n-space
--   OO_Pn : the structure sheaf of Pn
--    F(d) : the sheaf twisted by d
-- Omega^1 : the sheaf of differen
-- Omega^i : the ith exterior power of Omega^i
--  F ++ G : the direct sum of sheaves F and G
--     a*F : the direct sum of a copies of a sheaf F

-* rational surfaces *-

cubicScroll=method()
-- A cubic scroll (B1.4)
--     PURPOSE : Construct a cubic scroll, a rational surface of degree 3 in a projective fourspace P4
--       INPUT : 'P4', the ring of P4
--      OUTPUT : an ideal 
-- DESCRIPTION : The function constructs a cubic scroll surface as the determinantal variety of a 2x3 matrix with linear entries in 'P4'
cubicScroll(PolynomialRing) := P4 -> minors(2,matrix{{P4_0,P4_1,P4_3},{P4_1,P4_2,P4_4}})
///

///
veroneseSurface=method()
-- A Veronese surface (B1.6) 
--     PURPOSE : Construct a veronese surface, a rational surface of degree 5 in a projective fourspace
--       INPUT : 'P4', the ring of P4
--             : 'P2', the ring of P2
--      OUTPUT : an ideal 
-- DESCRIPTION : The function constructs the surface as the projection of the the Veronse embedding of the projective plane 'P2' to projective fivespace with a general vertex
veroneseSurface(PolynomialRing,PolynomialRing) := (P4,P2) -> (
    -- 'kk' is the coefficient ring of 'P2'
    kk := coefficientRing P2;
    -- 'h' is the polynomial map represented by four random plane qudratics 
    h:=basis(2,P2)*syz random(kk^1,kk^6);
    -- 'X' is the image of 'P2' under 'h'
    X:=trim ker map(P2,P4,h);
    -- Check whether 'X' is a surface of degree 4 
    assert(degree X ==4 and dim X==3);
    X)

delPezzoSurface=method()
-- A Del Pezzo surface of degree 4 (B1.5) 
--        PURPOSE : Construct a Del Pezzo surface of degree 4 in a projective fourspace P4
--          INPUT : 'P4', the ring of P4
--         OUTPUT : an ideal 
--    DESCRIPTION : The function constructs a Del Pezzo surface as a complete intersection of two quadrics
--        COMMENT : If the user chooses the pair of the ring 'P4' of P4 and the ring 'P2' of P2 as input, then the function constructs a Del Pezzo surface as the blow-up of P2 at four points
delPezzoSurface(PolynomialRing) := P4 -> ideal random(P4^1,P4^{2:-2})
delPezzoSurface(PolynomialRing,PolynomialRing) := (P4,P2) -> (
    -- 'kk' is the coefficient ring of 'P2'
    kk:= coefficientRing P2;
    -- 'pts2' is the union of the three coordinate points and a random point on "P2' 
    pts := {matrix{{1,0,0}},matrix{{0,1,0}},matrix{{0,0,1}},matrix{{1,1,1}},random(kk^1,kk^3)};
    pts2:= intersect apply(pts, pt-> ideal((vars P2)* (syz pt)));
    -- 'h' is the polynomial map represented by plane cubics passing though the four points
    h:=gens truncate(3,pts2);
    -- 'X' is the image of 'P2' under 'h'
    X:=trim ker map(P2,P4,h);
    -- Check whether 'X' is a surface of degree 4 
    assert(degree X ==4 and dim X==3);
    X)

castelnuovoSurface=method()
-- A Castelnuovo surface (B1.7)
--     PURPOSE : Construct a Castelnouvo surface, a rational surface of degree 5 in a projective fourspace P4
--       INPUT : 'P4', the ring of P4
--      OUTPUT : an ideal 
-- DESCRIPTION : The function constructs a cubic scroll surface as the determinantal variety of a 3x2 matrix with linear and quadratic entries in 'P4'
castelnuovoSurface(PolynomialRing) := P4 -> minors(2,random(P4^{-2,2:-3},P4^{2:-4}))

bordigaSurface=method()
-- A Bordiga surface (B1.8)
--        PURPOSE : Construct a Bordiga surface, a rational surface of degree 6 in a projective fourspace P4
--          INPUT : 'P4', the ring of P4
--         OUTPUT : an ideal 
--    DESCRIPTION : The function constructs the ideal of a Bordiga surface as the dependency locus of a 4x3 matrix with linear entries from 'P4'. If s is "Blow-up," then the function chooses ten points on the projective plane randomly and computes the image of the morphim determine by the linear system of cubics through the four points
--        COMMENT : If the user chooses the pair of the ring 'P4' of P4 and the ring 'P2' of P2 as input, then the function constructs a Del Pezzo surface as the blow-up of P2 at ten points
bordigaSurface(PolynomialRing) := P4 -> minors(3,random(P4^{4:-3},P4^{3:-4}))
bordigaSurface(PolynomialRing,PolynomialRing) := (P4,P2) -> (
    -- 'kk' is the coefficient ring of 'P4'
    kk:= coefficientRing P2;
    pts := {matrix{{1,0,0}},matrix{{0,1,0}},matrix{{0,0,1}},matrix{{1,1,1}}}|apply(6,c->random(kk^1,kk^3));
    -- 'pts2' is the union of the six points on "P2'
    pts2:= intersect apply(pts, pt-> ideal((vars P2)* (syz pt)));
    -- 'h' is the polynomial map represented by plane quartics passing through the ten points
    h:=gens truncate(4,pts2);
    -- 'X' is the image of 'P2' under 'h'
    X:=trim ker map(P2,P4,h);
    -- Check whether 'X' is a surface of degree 6
    assert(degree X ==6 and dim X==3);
    X)

ionescuOkonekSurfaceD7=method()
-- A rational surface of degree 7 (B1.9)
--     PURPOSE : Construct a rational surface of degree 7 and sectional genus 4 in a projective fourspace P4
--       INPUT : 'P4', the ring of P4
--      OUTPUT : an ideal 
-- DESCRIPTION : The function constructs a rational surface of degree 7 and sectional genus 4 via the linear system of plane sextics passing through five simple points and six double points on a plane   
ionescuOkonekSurfaceD7(PolynomialRing,PolynomialRing) :=(P4,P2) -> (
    -- 'sixPoints' is the list of six simple points
    sixPoints:=apply(6,i->ideal random(P2^1,P2^{2:-1}));
    -- 'fivePoints; is the list of five points 
    fivePoints:=apply(5,i->ideal random(P2^1,P2^{2:-1}));
    -- 'H' is the union of 'fivePoints' and the double points supported by the points in 'sixPoints' 
    H:= intersect (apply(sixPoints,p->p^2)|fivePoints);
    -- 'X' is the image of 'P2' under the polynomial map represented by five plane sextics passing through 'H'
    X:= trim ker map(P2,P4,gens H);
    -- Check whether 'X' is a surface of degree 7 and sectional genus 4
    assert(dim X==3 and  degree X==7 and sectionalGenus X==4);
    X)

okonekSurfaceD8S6=method()
-- A rational surface of degree 8 and sectional genus 6 (B1.11)
--     PURPOSE : Construct a rational surface of degree 8 and sectional genus 6 in a projective fourspace P4
--       INPUT : 'P4', the ring of P4
--             : 'E", the exterior algebra 
--      OUTPUT : an ideal 
-- DESCRIPTION : The function finds a morphism from 6*OO_P4(-1) to OO_P4 ++ Omega^1(1), and it constructs the ideal sheaf of a rational surface of degree 8 and sectional genus 6 as its dependency locus
--     COMMENT : This function uses the BGG package
okonekSurfaceD8S6(PolynomialRing,Ring) := (P4,E) -> (
    -- The transpose of 'm6x2' represents a morphism from the direct sum of six copies of OO_P4(-1) to OO_P4 ++ Omega^1(1) 
    m6x2:=random(E^6,E^{-2,-4});
    betti(T:=res(coker m6x2,LengthLimit=>3));
    -- -- 'X' is defined as the dependency locus of the aforementioned morphism 
    X:= saturate ideal syz symExt(T.dd_3,P4);
    -- Check whether 'X' is a surface of degree 8 and sectional genus 6
    assert(dim X==3 and  degree X==8 and  (genera X)_1==6);
    X)
-*
degree8OkonekSurface(PolynomialRing,PolynomialRing) := (P4,P2) -> (
    -- Output: A surface linked (3,4) to the Veronese surface
    Y:=veroneseSurface(P4,P2);
    ci:=ideal(gens Y*random(source gens Y,P4^{-3,-4}));
    X:=ci:Y;
    assert(dim X==3 and  degree X==8 and  (genera X)_1==6);
    X)
*-
///

needsPackage"NongeneralTypeSurfacesInP4"
kk=ZZ/nextPrime 10^4
P2=kk[y_0..y_2]
pencil=ideal(y_0*(y_1-y_2),y_1*(y_0-y_2))
decompose pencil

///

ionescuOkonekSurfaceD8S5=method()
-- A rational surface of degree 8 and sectional genus 5 (B1.10)
--     PURPOSE : Construct a rational surface of degree 8 and sectional genus 5 in a projective fourspace P4
--       INPUT : 'P4', the ring of P4
--             : 'P2', the ring of P2
--      OUTPUT : an ideal 
-- DESCRIPTION : The function constructs a rational surface of degree 8 and sectional genus 5 via the linear system of plane septics passing through one simple point and ten double points on a plane   
-- Maybe this is a Ionescu  Okonek surface -- fix rename
ionescuOkonekSurfaceD8S5(PolynomialRing,PolynomialRing) := (P4,P2) -> (
    -- 'H' is the union of one simple point and ten double points on a plane   
    H:= intersect (apply(10,i->(ideal random(P2^1,P2^{2:-1}))^2)|{ideal random(P2^1,P2^{2:-1})});
    -- 'X' is the image of 'P2' under the polynomial map represented by five plane sextics passing through 'H'
    X:= trim ker map(P2,P4,gens H);
    -- Check whether 'X' is a surface of degree 8 and sectional genus 5
    assert(dim X==3 and degree X==8 and sectionalGenus X==5);
    X)

degree8AlexanderSurface=method()
-- Maybe this is a Ionescu  Okonek surface -- fix rename
degree8AlexanderSurface(PolynomialRing,PolynomialRing) := (P4,P2) -> (
    H:= intersect (apply(10,i->(ideal random(P2^1,P2^{2:-1}))^2)|{ideal random(P2^1,P2^{2:-1})});
    X:= trim ker map(P2,P4,gens H);
    assert(dim X==3 and degree X==8 and sectionalGenus X==5);
    X)

nonspecialAlexanderSurface=method()
-- A rational surface of degree 9 and sectional genus 6 (B1.12)
--     PURPOSE : Construct a rational surface of degree 9 and sectional genus 6 in a projective fourspace P4
--       INPUT : 'P4', the ring of P4
--      OUTPUT : an ideal 
-- DESCRIPTION : The function finds a module M of finite length with Hilbert functions (3,5,1), and it constructs a rational surface of degree 9 and sectional genus 6 as the cokernel of the map from F := 6*OO to the sheafified first syzygy module Syz_1(M) of M.
--     COMMENT : If the user chooses the pair of the ring 'P4' of P4 and the ring 'P2' of P2 as input, then The function constructs a rational surface of degree 9 and sectional genus 6 via the linear system of plane curves of degree 13 passing through ten quadruple points
nonspecialAlexanderSurface(PolynomialRing) := P4 -> (
    -- Define a map 'L' : 'P4'^{3:-1,15:-2} -> 'P4'^{1:0} 
    betti(L :=matrix{{P4_0,P4_1,P4_2}}|random(P4^1,P4^{15:-2}));
    -- Define a map 'L2': P4'^{3:-1,15:-2} -> 'P4'^{3:-1} by concatenating the map from 'P4'^{3:-1} to 'P4'^{3:-1} and a randomly chosen map from 'P4'^{15:-2} to 'P4'^{3:-1} horizontally
    betti(L2 :=map(P4^{3:-1},P4^{3:-1},0)|random(P4^{3:-1},P4^{15:-2}));
    -- Concatenate the transposes of 'L' and 'L2' side by side and transpose the resulting map 'N'
    betti (N:=transpose (transpose L| transpose L2));
    -- Compute the resolution of 'N'. 
    betti (fN:=res coker N);
    -- The transpose of the 4th differential of 'fN' is the presentation matrix of the first syzygy module Syz_1(M) of M. The surface 'X' is defined to be the cokernel of a map from 6*OO to Syz_1(M) 
    X:=trim ideal (fN.dd_4*syz fN.dd_4^{16..21});
    -- Check whether 'X' is a surface of degree 9 and sectional genus 6
    assert(dim X==3 and degree X==9 and sectionalGenus X==6);
    X)
nonspecialAlexanderSurface(PolynomialRing,PolynomialRing) := (P4,P2) -> (
    -- 'h1' is the ideal of ten quadruple points
    betti(h1:=intersect apply(10,c->(ideal random(P2^1,P2^{2:-1}))^4));
    -- 'X' is the image of 'P2' under the map associated with the linear system of degree-10 curves passing through the quadruple points
    X:=trim ker map(P2,P4,(gens h1)_{0..4});
    -- Check whether 'X' is a surface of degree 9 and sectional genus 6
    assert(dim X==3 and degree X==9 and sectionalGenus X==6);
    X)

enriquesSurfaceOfDegree9=method()
-- Comment: the 12 quadrics are dual to 3 quadrics in dual space
--          hence define a canonical curve of genus 5. Since the Enriques surface
--          is blown-up in precisely one point, we get a birational map
--          M_5 -> U, where U is the universal family over M_E of Enriques surfaces
enriquesSurfaceOfDegree9(PolynomialRing) := P4 -> (
    N:=random(P4^1,P4^{12:-2});-- twelve quadrics
    betti (fN:=res coker N);
    X:=trim ideal (fN.dd_4*syz fN.dd_4^{15..20});
    assert(dim X==3 and degree X==9 and sectionalGenus X==6);
    X)

specialityOneAlexanderSurface=method()
-- A rational surface of degree 9 and sectional genus 7 (B1.13)
--     PURPOSE : Construct a rational surface of degree 9 and sectional genus 7 in a projective fourspace P4
--       INPUT : 'P4', the ring of P4
--             : 'E', the exterior algebra
--      OUTPUT : an ideal 
-- DESCRIPTION : The function finds a morphism from F = Omega^3(3) ++ Omega^2(2) to G = 2*Omega^1(1)++OO_P4, and it constructs the ideal sheaf of a rational surface of degree 9 and sectional genus 7 as its dependency locus 
--    COMMENTS : This function uses the command 'symExt' in the BGG package. This may fail if the characteristic of the field is small 
specialityOneAlexanderSurface(PolynomialRing,Ring) := (P4,E) -> (
    b1:=gens trim ideal(basis(2,E)%ideal(E_0,E_1))|matrix{{E_0,E_1}};
    -- 'bb' is a graded E-module homomorphism from 'E'^{1:0,1:-1} to 'E'^{3:-2,2:-1}, which represents a morphism from G^* to F^*
    bb:=b1||random(E^{1},source b1);
    -- Compute the syzygies of 'bb', whose transpose corresponds to the morphism from F to G
    T:=res(coker bb,LengthLimit=>3);
    -- 'X' is defined as the cokernel of the morphism from F to G
    X:=trim saturate ideal syz symExt(T.dd_3,P4);
    -- Check whether 'X' is a surface of degree 9 and sectional genus 7
    assert(dim X==3 and degree X== 9 and sectionalGenus X==7);
    X)

degree10pi8RanestadSurface=method()
-- A rational surface of degree 10 and sectional genus 8 (B1.14)
--     PURPOSE : Construct a rational surface of degree 10 and sectional genus 8 in a projective fourspace P4
--       INPUT : 'P4', the ring of P4
--      OUTPUT : an ideal 
-- DESCRIPTION : The function finds a suitable morphism from 5*OO_P4(1) ++ 2*OO_P4 to 2*OO_P4(2) and its cokernel M, and it constructs the ideal sheaf of a rational surface of degree 10 and sectional genus 8 as the dependency locus of a morphism from F = Omega^3(3) to the first syzygy module G of M
--    COMMENTS : See the paper (need to specify it) for motivation of this construction and compare with enriquesSurfaceOfDegree10. See the paper for motivation of this construction and compare with enriquesSurfaceOfDegree10
degree10pi8RanestadSurface(PolynomialRing) := P4 -> (
    -- Define a morphism 'a1' from 5*OO_P4 to 2*OO_P4(1)  
    a1:=transpose matrix apply (5,i->{P4_i,random(0,P4)*P4_i});
    -- Define a morphism 'a2' from 2*OO_P4(-1) to 2*OO_P4(1)  
    a2:=map(P4^1,P4^{2:-2},0)||matrix{{sum(3,i->random(0,P4)*P4_i^2),sum(2,i->random(0,P4)*P4_(i+3)^2)}};
    -- Concatenate 'a_1' and 'a2' horizontally to create a morphism 'aa' from 5*OO_P4 ++ 2*OO_P4(-1) to 2*OO_P4(1)  
    aa:=map(P4^2,,a1|a2);
    -- Compute a resolution of 'aa' up to length 4
    faa:=res(coker aa,LengthLimit=>4);
    -- Define 'b1' to be a 15x14 submatrix of 'faa.dd_3'
    b1:=faa.dd_3^{0..14}_{0..13};
    -- 'm15x5' induces a map from Omega^3(3) to the sheafified first syzygy module Syz_1(M) of the cokernel M of aa
    m15x5:=syz transpose syz (transpose (b1*random(source b1,P4^{1:-4})),DegreeLimit=>-3);
    -- 'X' is defined as the dependency locus of a map from Omega^3(3) to Syz_1(M)
    X:= trim ideal(transpose (syz transpose (faa.dd_2_{0..14}*m15x5))_{2}*faa.dd_2);
    -- Check whether 'X' is a surface of degree 10 and sectional genus 8
    assert(dim X==3 and degree X==10 and sectionalGenus X==8);
    X)

enriquesSurfaceOfDegree10=method()
-- see the paper for motivation of this construction and compare with degree10pi8RanestadSurface
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
///
tex betti res coker random(P4^{2:-2},P4^{5:-3,2:-4})
tex betti res coker random(P4^{2:-2},P4^{5:-3})
///

degree10pi9RanestadSurface=method()
-- A rational surface of degree 10 and sectional genus 9 (B1.16)
--     PURPOSE : Construct a rational surface of degree 10 and sectional genus 9 in a projective fourspace P4 with one 6-secant line
--       INPUT : 'P4', the ring of P4
--             : 'E', the exterior algebra
--      OUTPUT : an ideal 
-- DESCRIPTION : The function constructs the ideal sheaf of a rational surface of degree 10 and sectional genus 9 as the dependency locus of the morphism from F = 2*Omega^3(3) to G = OO_P4 ++ Syz_1(M), where M is the cokernel of a morphism from 
--    COMMENTS : See the paper (need to specify it) for motivation of this construction and compare with enriquesSurfaceOfDegree10
--               using the Tate resolution simplifies the construction
degree10pi9RanestadSurface(PolynomialRing,Ring) := (P4,E) -> (
    -- In the next two lins, construct an 'E'-module homomorphism 'a2' from 'E'^{2:-2} ++ 'E'^{2:-3}' to 'E'^{2:0}, whose transpose corresponds to a map 2*Omega^3(3) -> 2*Omega^1(1) ++ 2O.  
    a1:=(syz matrix{{E_0,E_1}})*random(E^{3:-1},E^{2:-2});
    a2:=map(E^2,,random(E^2,E^{2:-3})|transpose a1);
    -- Compute the resolution of the cokernel of 'a2' up to length 4
    T :=res(coker a2,LengthLimit=>4);
    -- Define the ideal sheaf of 'X' by computing its presentation matrix corresponding to the differential 'T.dd_4' of 'T' 
    X := saturate ideal syz symExt(T.dd_4,P4);
    -- Check whether 'X' is a surface of degree 10 and sectional genus 9
    assert(dim X ==3 and degree X==10 and sectionalGenus X==9);
    X)

degree10DESSurface=method()
-- A rational surface of degree 10 and sectional genus 9 (B1.15)
--     PURPOSE : Construct a rational surface of degree 10 and sectional genus 9 in a projective fourspace P4 with no 6-secant lines
--       INPUT : 'P4', the ring of P4
--             : 'E', the exterior algebra
--      OUTPUT : an ideal 
-- DESCRIPTION : The function finds a morphism from F = 2*Omega^3(3) to G = 2*Omega^1(1) ++ OO_P4 and constructs constructs the ideal sheaf of a rational surface of degree 10 and sectional genus 9 as its dependency locus
--    COMMENTS : The function uses the command 'symExt' in the BGG package
degree10DESSurface(PolynomialRing,Ring) := (P4,E) -> (
    -- Define a map bb: 2*'E'(-2)++'E'(-3) -> 2'E', whose transpose can be interpreted as a map from F to G
    bb:=random(E^2,E^{2:-2,-3});
    -- Compute the resolution of 'bb' up to length 3
    betti (T:= res(coker bb,LengthLimit=>3));
    -- Define the ideal sheaf of 'X' by computing its presentation matrix corresponding to the differential 'T.dd_4' of 'T' 
    -- %The function symExt from the package BGG computes from a differential in a Tate resolution
    -- %above the regularity (hence a linear differential)
    -- %over the exterior algebra E the linear presentation matrix
    -- %of the corresponding sheaf on P4 (and vice versa from P4-modules to E-modules).
    X := saturate ideal syz symExt(T.dd_3,P4);
    -- Check whether 'X' is a surface of degree 10 and sectional genus 9
    -- %In this particular case symExt(T.dd_3,P4) is a 28x15 matrix whose kernel has rank 1
    -- %and is given by the quintics in the ideal of desired X.
    assert(dim X ==3 and degree X==10 and (genera X)_1==9);
    X)
///
kk=ZZ/nextPrime 10^4
P4=kk[x_0..x_4]
E=kk[e_0..e_4,SkewCommutative=>true]
X=degree10DESSurface(P4,E);
minimalBetti X
(degree X, sectionalGenus X, chiO(X))
betti tateResolutionOfSurface X


///

popescuSurface=method()
-- every thing is determined by the map aa which is part of a differential in the Tate resolution
-- and a random choice to get bb, a differential in the Tate resolution. 
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
    --betti tateResolutionOfSurface X
    assert(dim X==3 and degree X==11 and (genera X)_1==11);
    X)

vBELSurface=method()

vBELSurface(Ring,Ring) := (P4,P2) -> ( -- the specific surface from the vBEL paper
    -- A rational surface (from the vBEL paper) obtained via a linear system in the plane with assigned baselocus.
    --     PURPOSE : Construct a nonsingular rational surface of degree 11 and sectional genus 11 over a field of characteristic 2
    --       INPUT : 'P4' and 'P2', the homogeneous coordinate rings of projective fourspace and the projective plane, both in characteristic 2.
    --      OUTPUT : Ideal of the rational surface of degree 11
    -- DESCRIPTION : This function outputs the ideal of a rational surface as the image of a rational map from the projective plane

    if char P4 !=2 then error "expect a ground field of caharcteristic 2";
    if char P2 =!= char P4 then error "P2 and P4 should have the same characteristic 2";
    t:= symbol t;
    --define a finite field with 2^14 elements
    FF14:=ZZ/2[t]/ideal(t^14+t^13+t^11+t^10+t^8+t^6+t^4+t+1);
    --define the homogeneous coordinate ring of the projective plane over 'FF14'
    P2FF14:=FF14[gens P2];
    --define a FF14-rational point in  'P2FF14'
    Q:=ideal(vars P2FF14*syz matrix{{t^11898,t^137, 1}});
    --define a finite field with 2^5 elements
    FF5:=ZZ/2[t]/ideal(t^5 +t^3 +t^2 +t +1);
     --define the homogeneous coordinate ring of the projective plane over 'FF5'
    P2FF5:=FF5[gens P2];
    --define FF5-rational point in 'P2FF5'
    R:=ideal(vars P2FF5*syz matrix{{t^6 ,t^15, 1}});
    -- define the orbits of 'Q' under the Frobenius endomorphism in 'P2'
    Q14:=ker map(P2FF14/Q,P2);
     -- define the orbits of 'R' under the Frobenius endomorphism in 'P2'
    R5:=ker map(P2FF5/R,P2);
    -- define a point in 'P2' 
    P:=ideal(P2_0,P2_1);
    -- define the ideal of forms triple at 'P', double along 'Q14' and simple in 'R5'
    H:=intersect(saturate(Q14^2),R5,P^3);
    -- the five generators of 'H' of degree 9 define a rational map to 'P4' with image 'X' 
    X:=ker map(P2,P4,(gens H)_{0..4});
    --'X' is a smooth surface of degree 11 and sectional genus 11.
    assert(dim(X+minors(2, jacobian X))==0);
    X)




vBELSurface(PolynomialRing) := P4 -> (
    -- A rational surface obtained via a linkage.
    --     PURPOSE : Construct a nonsingular rational surface of degree 11 and sectional genus 11 
    --       INPUT : 'P4', the homogeneous coordinate rings of projective fourspace 
    --      OUTPUT : Ideal of the rational surface of degree 11
    -- DESCRIPTION : This function outputs the ideal of a rational surface as linked to a reducible surface of degree 7

    kk:= coefficientRing P4;
    u := symbol u;
    --define the homogeneous coordinate ring of the projective plane over 'kk'
    P2:=kk[u_0..u_2];
    --define the ideal of the three coordinate points in the plane
    coordinatepoints:=ideal(u_0*u_1,u_0*u_2,u_1*u_2);
    --define the ideal of five general points in the plane 
    fivepoints:=minors(2,random(P2^2,P2^{2:-1,-2}));
    --define the unique quartic form double along 'p123' and simple along 'p5'
   specialplanequartic:=ideal(gens(saturate intersect(coordinatepoints^2,fivepoints)))_{0};
-- define the ideal of intersection of a line through a coordinate point (1:0:0) and 'specialplanequartic'
   fourpoints:=ideal(u_1+u_2)+specialplanequartic;
   --define the two points in 'fourpoints' outside the coordinate point (1:0:0)
   twopoints:=fourpoints:coordinatepoints^2;-- two points in line through (1:0:0)
   --define the ideal of ten points:  the union of 'coordinatepoints','fivepoints' and 'twopoints'.
   tenpoints:=saturate(intersect(twopoints,coordinatepoints,fivepoints));
   --check that the Hilbert Burch matrix of 'tenpoints' is a 4x5-matrix with linear entries
   assert(betti res tenpoints==new BettiTally from {(0,{0},0) => 1, (1,{4},4) => 5, (2,{5},5) => 4});
   -- define the rational map defined by the five quartic generators of 'tenpoints' to P4
   F:=map(P2,P4,gens tenpoints);
   -- define the image of 'F', a Bordiga surface (of degree 6 and sectional genus 3)
   bordiga:=kernel F;--Bordiga surface
   --define the image by 'F' in 'bordiga' of the line through 'twopoints', this is a (-2)-line on 'bordiga'
   minus2line:=preimage (F,ideal(u_1+u_2));--a (-2)-line in s6
   --define the image by 'F' in 'bordiga' of the 'specialplane quartic' (which is also in 'tenpoints'), it is a twisted cubic curve in 's6' 
   twistedcubic:=preimage (F,specialplanequartic);--a twisted cubic curve in 'bordiga'
   hyp3:=ideal(gens twistedcubic)_{0}+bordiga;--the hyperplane section of 'bordiga' containing 'twistedcubic'
   --the ideal of three exceptional lines in 'bordiga' over the 'coordinatepoints', the lines in the hyperplane section of 's6' that contains the twisted cubic curve 's622'
  threelines:=hyp3:twistedcubic;--three (-1)-lines residual to twistedcubic in 'hyp3'
   xline0:=preimage (F,ideal (u_1^2,u_2*u_1,u_2^2));
   --the (-1)-line in 'bordiga' over (1:0:0) 
   line0:=ideal (gens xline0)_{0..2};
--the ideal of the point of intersection between the exceptional line over (1:0:0) and the (-2)-line 'minus2line'
   point1:=saturate(minus2line+line0);--the point of intersection between 'minus2line' and a line in 'threelines'
   dpoint1:=vars P4* gens kernel(diff(vars P4,transpose gens point1));
-- the ideal of the tangent plane section at 'point1' of the unique quadric surface that contains the three lines 'threelines'
   twolines:=ideal(gens threelines)_{0..1}+ideal flatten diff( dpoint1, (gens threelines)_{1});
   --the ideal of the line residual to 'line0' in 'twolines'; a line that passes through 'point1' and meet all three lines in 'threelines'
   line3:=twolines:line0;-- a trisecant line to 'bordiga' through 'point1'
--the 'line3' intersect all 'threelines' 
--the ideal of the union of the (-2)-line 'minus2line' and the line 3-secant line 'line3', they both pass through 's61200'
twolines1:=saturate intersect(minus2line,line3);
 --the plane spanned by the 'minus2line' and 'line3' 
   plane:=ideal (gens (saturate intersect(minus2line,line3)))_{0..1};
   -- the quadric surface containing the 'threelines'
   quadricsurface:=ideal(gens threelines)_{0..1}; 
--a reducible surface, the union of 'plane','quadricsurface' and 'bordiga', of degree nine.
   Y9:=saturate intersect (plane,quadricsurface, bordiga);--a surface of degree 9
   --check that the ideal of 's9' is generated by a unique quartic and 12 quintic forms 
   assert(minimalBetti Y9== new BettiTally from {(0,{0},0) => 1, (1,{4},4) => 1, (1,{5},5) => 12, (2,{6},6) => 23, (3,{7},7) => 14, (4,{8},8) => 3}); -- proceed if it is contained in one quartic
   ci45:=ideal (gens Y9 * random(source gens Y9, P4^{-4,-5}));
   --define a surface as linked to 's9' in a complete intersection (4,5)
   X:=ci45:Y9;-- A surface of degree 11, genus 11
   assert( (dim X, degree X, (genera X)_1)==(3,11,11));
   X)


-- presumably not used
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
-- Most surfaces are 6 regular, if not one has truncate at the real regularity,
-- the n in the second version
tateResolutionOfSurface(Ideal) := X -> (
    if not (dim X==3 and codim X==2) then error "expected the ideal of a surface in P4";
    P4:= ring X;
    kk:=coefficientRing P4;
    e:=symbol e;
    E:=kk[e_0..e_4,SkewCommutative=>true];
    m:=syz gens truncate(6,X);
    -- see BGG for the documentation of symExt
    m':=symExt(m,E);
    T1:=res(coker m',LengthLimit=>8);
    T:=(dual T1)[-7]**E^{-6})

tateResolutionOfSurface(Ideal,ZZ) := (X,n) -> (
    if not (dim X==3 and codim X==2) then error "expected the ideal of a surface in P4";
    P4:= ring X;
    kk:=coefficientRing P4;
    e:=symbol e;
    E:=kk[e_0..e_4,SkewCommutative=>true];
    m:=syz gens truncate(n,X);
     -- see BGG for the documentation of symExt
    m':=symExt(m,E);
    T1:=res(coker m',LengthLimit=>n+2);
    T:=(dual T1)[-n-1]**E^{-n})
///
kk=ZZ/nextPrime 10^4
P4=kk[x_0..x_4]
X=K3surfaceD10S9L1 P4;
X=ellipticSurfaceD12S14Linfinite P4;
minimalBetti X
T=tateResolutionOfSurface X;
betti T
betti tateResolutionOfSurface(X,7)

///

tangentToMonad = method();
-- DESCTRIPTION : This command computes the dimension of the tangent space to the space 'M' of monads of the form a*OMega^3(3)->b*Omega^2(2)++c*Omega^1(1)->d*OO at a specfic example
--                by taking the derivative of the composite of differentials. The dimension of the space of isomophism classes of monads is
--                dim (M)-(a^2+b^2+c^2+5*b*c+d^2-1). 
tangentToMonad(Ideal) := X -> (
    assert(regularity X <= 6);
    KK := coefficientRing ring X;
    pX := syz gens X;
    e := symbol e;
    E := KK[e_0..e_4,SkewCommutative => true];
    T := tateResolution(pX,E,3,8);
    beta := (T.dd_4)^(positions(degrees target T.dd_4,i->i=={-4}));
    alpha := (T.dd_5)_(positions(degrees source T.dd_5,i->i=={-1}));
    nrowsBeta := (tally degrees target beta)_{-4};
    ncolsBeta := (tally degrees source beta)_{-3};
    ncolsBeta' := (tally degrees source beta)_{-2};
    ncolsAlpha := (tally degrees source alpha)_{-1};
    n1 := nrowsBeta*ncolsBeta;
    n2 := nrowsBeta*ncolsBeta';
    n3 := ncolsBeta*ncolsAlpha;
    n4 := ncolsBeta'*ncolsAlpha;
    a := symbol a;
    b := symbol b;
    c := symbol c;
    d := symbol d;
    R := KK[a_(0,0)..a_(nrowsBeta-1,ncolsBeta-1),
	b_(0,0)..b_(nrowsBeta-1,ncolsBeta'-1),
	c_(0,0)..c_(ncolsBeta-1,ncolsAlpha-1),
	d_(0,0)..d_(ncolsBeta'-1,ncolsAlpha-1),
	e_0..e_4,
	Degrees=>{n1:1,n2:2,n3:1,n4:2,5:1},
	SkewCommutative => true];
    salpha := substitute(alpha,R);
    sbeta := substitute(beta,R);
    beta' := matrix table(nrowsBeta,ncolsBeta,(i,j)->a_(i,j)) | matrix table(nrowsBeta,ncolsBeta',(i,j)->b_(i,j));
    alpha' := matrix table(ncolsBeta,ncolsAlpha,(i,j)->c_(i,j)) || matrix table(ncolsBeta',ncolsAlpha,(i,j)->d_(i,j));
    gamma := map(flatten (sbeta*alpha'+beta'*salpha));
    delta := map(E^{nrowsBeta*ncolsAlpha:-3},,sub(contract(matrix{{a_(0,0)..a_(nrowsBeta-1,ncolsBeta-1),
			b_(0,0)..b_(nrowsBeta-1,ncolsBeta'-1),
			c_(0,0)..c_(ncolsBeta-1,ncolsAlpha-1),
			d_(0,0)..d_(ncolsBeta'-1,ncolsAlpha-1)}},transpose gamma),E));
    mu := syz(delta);
    super basis(6,image mu)
    )

tangentToMonad(Matrix,Matrix) := (alpha,beta) -> (
    E := ring alpha;
    KK := coefficientRing E;
    nrowsBeta := (tally degrees target beta)_{-4};
    ncolsBeta := (tally degrees source beta)_{-3};
    ncolsBeta' := (tally degrees source beta)_{-2};
    ncolsAlpha := (tally degrees source alpha)_{-1};
    n1 := nrowsBeta*ncolsBeta;
    n2 := nrowsBeta*ncolsBeta';
    n3 := ncolsBeta*ncolsAlpha;
    n4 := ncolsBeta'*ncolsAlpha;
    a := symbol a;
    b := symbol b;
    c := symbol c;
    d := symbol d;
    R := KK[a_(0,0)..a_(nrowsBeta-1,ncolsBeta-1),
	b_(0,0)..b_(nrowsBeta-1,ncolsBeta'-1),
	c_(0,0)..c_(ncolsBeta-1,ncolsAlpha-1),
	d_(0,0)..d_(ncolsBeta'-1,ncolsAlpha-1),
	E_0..E_4,
	Degrees=>{n1:1,n2:2,n3:1,n4:2,5:1},
	SkewCommutative => true];
    salpha := substitute(alpha,R);
    sbeta := substitute(beta,R);
    beta' := matrix table(nrowsBeta,ncolsBeta,(i,j)->a_(i,j)) | matrix table(nrowsBeta,ncolsBeta',(i,j)->b_(i,j));
    alpha' := matrix table(ncolsBeta,ncolsAlpha,(i,j)->c_(i,j)) || matrix table(ncolsBeta',ncolsAlpha,(i,j)->d_(i,j));
    gamma := map(flatten (sbeta*alpha'+beta'*salpha));
    delta := map(E^{nrowsBeta*ncolsAlpha:-3},,sub(contract(matrix{{a_(0,0)..a_(nrowsBeta-1,ncolsBeta-1),
			b_(0,0)..b_(nrowsBeta-1,ncolsBeta'-1),
			c_(0,0)..c_(ncolsBeta-1,ncolsAlpha-1),
			d_(0,0)..d_(ncolsBeta'-1,ncolsAlpha-1)}},transpose gamma),E));
    mu := syz(delta);
    super basis(6,image mu)
    )



-* schreyer surfaces *-

moduleFromSchreyerSurface=method()
-- computes the H^1-module of the ideal sheaf
moduleFromSchreyerSurface(Ideal) := X -> (
    betti(fX:=res X);
    betti (fN:=res(coker transpose fX.dd_4));
    ideal fN.dd_5)

schreyerSurfaceFromModule=method()
-- computes a surface with given H^1-module M.
-- M is known to lead to a smooth surface.
schreyerSurfaceFromModule(Ideal) := M -> (
    P4:= ring M;
    fM:=res(M);
    kk:=coefficientRing ring M;
    rows:=positions(degrees fM_3,d->d=={4});
    columns:=positions(degrees fM_2,d->d=={3});
    N:=(fM.dd_3)^columns_rows;
    while( -- get a smooth surface
	while( -- get a surface
	    while( -- check that the linear 10x2 transposed matrix has kk^2 as a cokernel
		n1:=random(kk^(rank source N),kk^2);
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
--Input: P4: coordinate ring of P4
--       s: integer desired number of extra syzygies
-- Output: X, homogenous ideal of a surface of degree 11 sectionalGenus 10 and pg=q=0.
--           is either rational or non-minimal Enriques
-- Method: search for a H^1-module M with s extra syzygies leading to a surface X, so s>=2.
schreyerSurface(Ring,Number) := opt -> (P4,s) -> (
    if s<2 then error "need s>=2 extra syzygies in the construction";
    F:=res(ideal vars P4, LengthLimit=>3);
    kk:=coefficientRing P4;
    M:=null;fM:=null;N:=null;N1:=null; X:=null; singX:=null;
    trials:=1; 
    countSmooth:=1; count:=1; countMonad := 1; countModule := 1; 
    while( --smooth
	while( -- monad ok
	    while( -- module ok
		while ( -- module tested for s extra syzygies
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
--Input: P4: coordinate ring of P4
--       s: integer desired number of extra syzygies
-- Output: X, homogenous ideal of a surface of degree 11 sectionalGenus 10 and pg=q=0.
--          if X is smooth then X is either rational or non-minimal Enriques
-- Method: search for a H^1-module M with s extra syzygies leading to a surface X, so s>=2.
findRandomSchreyerSurface(Ring) := P4 -> (
    findRandomSchreyerSurface(P4,2))

findRandomSchreyerSurface(Ring,Number) := (P4,s) -> (
    --Input: P4: coordinate ring of P4
    --       s: integer desired number of extra syzygies
    -- Output: X, homogenous ideal of a surface of degree 11 sectionalGenus 10 and pg=q=0.
    --           is either rational or non-minimal Enriques
    -- Method: search for a H^1-module M with s extra syzygies leading to a surface X, so s>=2.

    F:=res(ideal vars P4, LengthLimit=>3);
    kk:=coefficientRing P4;
    M:=null;fM:=null;N:=null;N1:=null;
    while( -- phi: sF ->sG drops rank in expected codimension => degree X is ok
    while( -- the sheaf sF is the syzygy sheaf of two copies of kk
      while ( -- get s extra syzygies
	while (-- hilbert function ok
	    M=ideal (F.dd_3*random(F_3,P4^{-4}));
          apply(4,i->hilbertFunction(i,M))!={1,5,5,0}) do ();
	fM=res(M,DegreeLimit=>1,LengthLimit=>3);
	rank fM_3 <s) do ();
        while ( -- non-zero s'x2 matrix where s'>=s
	    N1=random(P4^{rank fM_3:-4},P4^{2:-4});
	  coker transpose N1 !=0) do ();
      N = coker transpose (fM.dd_3*N1);
      (dim N , degree N)!=(0,2)) do ();
    J1:=syz transpose (fM.dd_2*syz transpose syz(transpose(fM.dd_3*N1),DegreeLimit=>-3));
    source J1 != P4^{0,-2}) do ();
    trim ideal(transpose J1_{1}*syz(fM.dd_1))
    )
findRandomSmoothSchreyerSurface=method(Options=>{Verbose=>true})

findRandomSmoothSchreyerSurface(Ring,Number) := opt -> (P4,s) -> (
    -- Input: P4: coordinate ring of P4
    --       s: integer desired number of extra syzygies
    -- Output: X, homogenous ideal of a surface of degree 11 sectionalGenus 10 and pg=q=0.
    --           is either rational or non-minimal Enriques
    -- Method: search for a H^1-module M with s extra syzygies leading to a surface X, so s>=2.

    X:=null;singX:=null;
    count:=1;
    while (  -- smooth surface
	if opt.Verbose then (
	elapsedTime while ( -- only hypersurface singularities
	    X=findRandomSchreyerSurface(P4,s);
	    dim (X+ideal jacobian X)!=0) do (count=count+1);
	    <<count <<endl;) else (
        while ( -- only hypersurface singularities
	    X=findRandomSchreyerSurface(P4,s);
	    dim (X+ideal jacobian X)!=0) do (count=count+1););	
	singX=X+minors(2,jacobian X);
	 dim singX !=0) do ();
   X)

/// -* oes not exists *-
kk=ZZ/nextPrime(10^3)
P4=kk[x_0..x_4]
elapsedTime X=unirationalConstructionOfSchreyerSurfaces(P4,KodairaDimension=>-1);
minimalBetti X
M=moduleFromSchreyerSurface X;
minimalBetti M
tangentDimension M
///



collectSchreyerSurfaces=method()
-- Input: adjTypes, List of adjunction types
--        Ms, List of H^1-modules
--        N, integer, desired number of H^1-modules
-- Output
collectSchreyerSurfaces(List,List,Number) :=(adjTypes,Ms,N) -> (
    -- the same as
    --            collectSchreyerSurfaces((adjTypes,Ms,2,N)
    -- collect N smooth surfaces
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
    -- either collect N smooth with at least s extra surfaces
    --     or discover a new family
    -- Input adjTypes, a list of already discovered adjunction type
    --       Ms, a list of H1-mudules M
    --       s: integer desired number of additional syzygies
    --       N: integer the desired number of new modules M    
    -- Output
    --      two new lists: adjTypes and Ms
    P4:=ring first Ms;
    adjTypes1:=adjTypes;
    adjTypes2:={};Ms2:={};
    Ms1:=Ms;
    count:=0; -- number of new adjunction types
    count1:=0; -- number of new modules
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
-- precompute modules and adjunction types produced by applying the function
-- collectSchreyerSurfaces and sorting by hand.
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
      {(4, 11, 10), 4, (9, 19, 11), 1, (10, 19, 10), 0, (9, 16, 8), 0, (7, 11, 5), 5, (4, 4, 1)},
      {(4,11,10), 3, (9,19,11), 1, (10,18,9), 2, (8,12,5), 4, (4,4,1)},
      {(4,11,10), 3, (9,19,11), 2, (10,18,9), 0, (8,13,6), 3, (5,6,2)},
      {(4,11,10), 2, (9,19,11), 3, (10,17,8), 2, (7,10,4), 2, (3,3,1)},
      {(4,11,10), 2, (9,19,11), 3, (10,17,8), 1, (7,10,4), 8, (3,2,0)},
      {(4,11,10), 2, (9,19,11), 2, (10,17,8), 4, (7,9,3), 7, (2,1,0)},
      {(4,11,10), 1, (9,19,11), 4, (10,16,7), 4, (6,7,2)},
      {(4,11,10), 0, (9,19,11), 6, (10,15,6), 5, (5,5,1)}};
    (Ms,adjTypes)
    )
///
restart
loadPackage"NongeneralTypeSurfacesInP4"
kk=ZZ/3
P4=kk[x_0..x_4]
X=specificSchreyerSurface(P4,1);
elapsedTime (L0,L1,L2,L3)=adjunctionProcess(X,5);
L0
///


specificSchreyerSurface=method()
--Input: k an integer
--Output a specific schreyer surface
specificSchreyerSurface(Ring,Number) := (P4,k) -> (
    (Ms,Types):=exampleOfSchreyerSurfaces(P4);
    X:=schreyerSurfaceFromModule(Ms_k);
    <<Types_k <<endl;
    X)

enriquesSurfaceD11S10 = method()
-- Get the precomputed enriques-schreyer surface
enriquesSurfaceD11S10(PolynomialRing) := P4 -> (
    if char P4 != 3 then error "Need a ground field of characteristic 3";
    X:=specificSchreyerSurface(P4,0)
    )

/// -* discovering a unirational construction in case k=7 by analyzing an example
       through linkage;  see schreyerSurfaceWith2LinearSyzygies *-
       
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


schreyerSurfaceWith2LinearSyzygies=method(Options=>{Smooth=>true})
-- corresponds to modules with s=4 extra syzygies
schreyerSurfaceWith2LinearSyzygies(Ring) := opt -> P4 -> (
    m2x3:=matrix{{P4_0,P4_1,P4_3},{P4_1,P4_2,P4_4}};
    scroll:=minors(2,m2x3);
    hypPlane:=ideal P4_1;
    lines1:={ideal(P4_4,P4_2,P4_1),ideal(P4_3,P4_1,P4_0),ideal(P4_2,P4_1,P4_0)};
    -- two rulings ond the directrix of the scroll
    q2x2 := matrix{{P4_0,P4_2}}||random(P4^1,P4^{2:-1})%hypPlane;
    quadric := hypPlane+minors(2,q2x2);
    -- a quadric surface with a ruling containing the directrix
    -- maybe check smoothness 
    Z:=intersect(scroll,quadric);
    assert(degree Z == 5);
    twoPointsa:=(decompose((quadric+scroll):lines1_2));
    if twoPointsa_0+lines1_0==twoPointsa_0 then twoPointsa=twoPointsa_{1,0};
    -- now twoPointsa_0 lies on lines1_1
    twoPointsb:={ideal(P4_4,P4_2,P4_1,P4_0),ideal(P4_3,P4_2,P4_1,P4_0)}; 
    twoLines:=apply(2,i->ideal (gens intersect(twoPointsa_i,twoPointsb_i))_{0..2});
    -- two disjoint lines.
    vertex:=ideal random(P4^1,P4^{4:-1}); --a general point
    twoPlanes:=apply(twoLines,l->ideal (gens intersect(l,vertex))_{0,1});
    -- cones over the two disjoint lines
    middlePlane:= null; conic:= null; twiceTwoPoints:=null; threePoints:= null;
    while( --get four points defined over kk
	middlePlane=trim sum apply(twoPlanes,p->ideal (gens p*random(source gens p,P4^{-1})));
	-- a plane through the vertex, meeting each of the two planes in a line.
	-- the middlePlane intersects Z in 5 points, which lie on a conic
	assert(betti saturate( middlePlane+Z)==
	    new BettiTally from {(0,{0},0) => 1, (1,{1},1) => 2, (1,{2},2) => 1, (1,{3},3) => 2});
	conic=ideal (gens saturate( middlePlane+Z))_{0..2};
	threePoints=saturate(middlePlane+scroll);
	assert(degree threePoints ==3);
	twiceTwoPoints=apply(2,i->decompose(twoPlanes_i+conic));
        not all(twiceTwoPoints,a->#a==2)) do (); -- this is not a unirational step, but a finite cover
    twoPoints:=apply(twiceTwoPoints,a->first a);
    -- apply(2,i->degree(twoPlanes_i+Z)==6)
    -- Each plane intersects the union Z in one of the two non-CM double point of Z   
    assert(degree  intersect({conic+Z}|twoPoints)==7);
    planeCubics:=apply(2,i->(p7:=saturate intersect(twoPlanes_i+Z,twoPoints_i);
	    twoPlanes_i+ideal(gens p7*random(source gens p7,P4^{-3}))));
    genus2Curve:=intersect(planeCubics|{conic});
    --netList primaryDecomposition genus2Curve;
    assert((dim genus2Curve, degree genus2Curve, genus genus2Curve)==(2,8,2));
    betti(p17:=saturate(Z+genus2Curve));
    assert((dim p17, degree p17)==(1,17)); -- 17 point
    betti (Z':=intersect(Z,genus2Curve));
    ci2:=ideal(gens Z'*random(source gens Z',P4^{2:-4}));
    --netList apply(2,i->tally apply(decompose  (ci2+twoPlanes_i),c->(dim c, degree c)));
    Y:=ci2:Z; 
    assert(degree Y==11);
    unionOfPlanes:=intersect(twoPlanes|{middlePlane});
    -- minimalBetti unionOfPlanes
    betti(Y':=intersect(Y,unionOfPlanes));
    assert((tally degrees source  gens Y')#{5}==2);
    ci:=ideal(gens Y')_{0,1};
    X:=ci:Y';
    assert((dim X, degree X, (genera X)_1) == (3,11,10));
    if opt.Smooth==true then (
	singX:=saturate(X+minors(2,jacobian X));
	<<"dim singX=" <<dim singX << endl;);
    return X;
    )

schreyerSurfaceWith2or3LinearSyzygies=method(Options=>{Smooth=>true})
schreyerSurfaceWith2or3LinearSyzygies(Ring,ZZ) := opt -> (P4,s) -> (
    if not member(s,{2,3}) then return error " expected s to be 2 or 3";
    m2x3:=matrix{{P4_0,P4_1,P4_3},{P4_1,P4_2,P4_4}};
    scroll:=minors(2,m2x3);
    hypPlane:=ideal P4_1;
    lines1:={ideal(P4_4,P4_2,P4_1),ideal(P4_3,P4_1,P4_0),ideal(P4_2,P4_1,P4_0)};
    -- two rulings ond the directrix of the scroll
    q2x2 := matrix{{P4_0,P4_2}}||random(P4^1,P4^{2:-1})%hypPlane;
    quadric := hypPlane+minors(2,q2x2);
    -- a quadric surface with a ruling containing the directrix
    -- maybe check smoothness 
    Z:=intersect(scroll,quadric);
    assert(degree Z == 5);
    twoPointsa:=(decompose((quadric+scroll):lines1_2));
    if twoPointsa_0+lines1_0==twoPointsa_0 then twoPointsa=twoPointsa_{1,0};
    -- now twoPointsa_0 lies on lines1_1
    twoPointsb:={ideal(P4_4,P4_2,P4_1,P4_0),ideal(P4_3,P4_2,P4_1,P4_0)}; 
    twoLines:=apply(2,i->ideal (gens intersect(twoPointsa_i,twoPointsb_i))_{0..2});
    -- two disjoint lines.
    vertex:=ideal random(P4^1,P4^{4:-1}); --a general point
    twoPlanes:=apply(twoLines,l->ideal (gens intersect(l,vertex))_{0,1});
    -- cones over the two disjoint lines
    middlePlane:= null; conic:= null; twiceTwoPoints:=null; threePoints:= null;
    while( --get four points defined over kk
	middlePlane=trim sum apply(twoPlanes,p->ideal (gens p*random(source gens p,P4^{-1})));
	-- a plane through the vertex, meeting each of the two planes in a line.
	-- the middlePlane intersects Z in 5 points, which lie on a conic
	assert(betti saturate( middlePlane+Z)==
	    new BettiTally from {(0,{0},0) => 1, (1,{1},1) => 2, (1,{2},2) => 1, (1,{3},3) => 2});
	conic=ideal (gens saturate( middlePlane+Z))_{0..2};
	threePoints=saturate(middlePlane+scroll);
	assert(degree threePoints ==3);
	twiceTwoPoints=apply(2,i->decompose(twoPlanes_i+conic));
        not all(twiceTwoPoints,a->#a==2)) do (); -- this is not a unirational step, but a finite cover
    twoPoints:=apply(twiceTwoPoints,a->first a);
    -- apply(2,i->degree(twoPlanes_i+Z)==6)
    -- Each plane intersects the union Z in one of the two non-CM double point of Z   
    assert(degree  intersect({conic+Z}|twoPoints)==7);
    if s==2 then  planeCubics:=apply(2,i->(p3:=saturate ((intersect(twoPlanes_i+scroll,twoPoints_i)):(twoPointsb_i));
	  saturate(intersect(twoLines_i,twoPlanes_i+ideal(gens p3*random(source gens p3,P4^{-2})))))) else (
    if s==3 then planeCubics=apply(2,i->(p4:=saturate intersect(twoPlanes_i+scroll,twoPoints_i);
	  saturate(intersect(twoLines_i,twoPlanes_i+ideal(gens p4*random(source gens p4,P4^{-2})))))));
    genus2Curve:=intersect(planeCubics|{conic});
    --netList primaryDecomposition genus2Curve;
    assert((dim genus2Curve, degree genus2Curve, genus genus2Curve)==(2,8,2));
    betti(p17:=saturate(Z+genus2Curve));
    assert((dim p17, degree p17)==(1,17)); -- 17 point
    betti (Z':=intersect(Z,genus2Curve));
    ci2:=ideal(gens Z'*random(source gens Z',P4^{2:-4}));
    --netList apply(2,i->tally apply(decompose  (ci2+twoPlanes_i),c->(dim c, degree c)));
    Y:=ci2:Z; 
    assert(degree Y==11);
    unionOfPlanes:=intersect(twoPlanes|{middlePlane});
    -- minimalBetti unionOfPlanes
    betti(Y':=intersect(Y,unionOfPlanes));
    assert((tally degrees source  gens Y')#{5}==2);
    ci:=ideal(gens Y')_{0,1};
    X:=ci:Y';
    assert((dim X, degree X, (genera X)_1) == (3,11,10));
    if opt.Smooth==true then (
	singX:=saturate(X+minors(2,jacobian X));
	<<"dim singX=" <<dim singX << endl;);
    return X;
    )




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
-- to be mentioned in the Moore matrix section
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
elapsedTime (X,m4x2)=aboRanestadSurface(P4,9,Special=>2,Verbose=>true);
minimalBetti X
elapsedTime  (L0,L1,L2,J)=adjunctionProcess(X,1);
L0=={(4, 12, 13), 8, (12, 24, 13)}

m4x2
E=ring m4x2
-*
m4x2n=m4x2^{0,1,2}||random(E^{2:1},E^{1:0})
Xn=aboRanestadSurfaceFromMatrix(P4,m4x2n,Verbose=>true);
-- does not give a surface
*-
X5=ideal (gens X)_{0..4};
R=X5:X;
dim R, degree R, minimalBetti R, degree (R+X)

--elapsedTime (X,m4x2)=aboRanestadSurface(P4,4,Special=>2,Verbose=>true); will not work
minimalBetti X
kk=ZZ/nextPrime 10^3
P4=kk[x_0..x_4]

elapsedTime (X,m4x2)=aboRanestadSurface(P4,7,Special=>2,Verbose=>true);
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

specificAboRanestadSurface=method()

specificAboRanestadSurface(PolynomialRing,Ring,Number) := (P4,E,k) -> (
    -- list of seven example ordered as in the paper.
    if char P4 == 19 then (       
    Ms:={matrix {{4*E_1+7*E_2+4*E_4, 4*E_0-9*E_1-9*E_2+4*E_3+3*E_4},
      {-2*E_0+3*E_1-5*E_2-3*E_3-6*E_4, E_0-5*E_1-9*E_2-8*E_3-7*E_4},
      {-9*E_0+5*E_1-7*E_2+3*E_3-7*E_4, -8*E_0+2*E_1-4*E_2+9*E_3-4*E_4},
      {8*E_0+7*E_1+E_2+2*E_3-7*E_4, -3*E_0+5*E_1+3*E_2+4*E_3-2*E_4}},
    matrix {{-E_0+7*E_1-6*E_2-4*E_3+4*E_4, -5*E_0-6*E_1+7*E_2-E_3+8*E_4},
      {6*E_0+7*E_1-3*E_2+9*E_3+4*E_4, -9*E_0-2*E_1+8*E_2-4*E_3+2*E_4},
      {E_0+9*E_1-5*E_2+5*E_3-9*E_4, -5*E_0+2*E_1-7*E_2-6*E_3-5*E_4},
      {-3*E_1-9*E_2+2*E_3+6*E_4, 6*E_1+E_2-4*E_3-7*E_4}},
    matrix {{-9*E_0-9*E_1+4*E_2-5*E_3+6*E_4,
      -9*E_0-8*E_1-9*E_2-5*E_3-4*E_4}, {-8*E_0-5*E_1-6*E_2-9*E_3+2*E_4,
      6*E_0-4*E_1-2*E_2+2*E_3+7*E_4}, {3*E_1+5*E_2+3*E_3+5*E_4,
      5*E_1+5*E_2+5*E_3+5*E_4}, {-8*E_0+3*E_1+7*E_2+4*E_3-3*E_4,
      -9*E_0+5*E_1+7*E_2-5*E_3-3*E_4}},
    matrix {{7*E_0+8*E_1-2*E_2+8*E_3+2*E_4, -8*E_0+8*E_1-8*E_2-E_3+8*E_4},
      {-7*E_0+4*E_1-6*E_2+7*E_3-2*E_4, 9*E_0+6*E_1-4*E_2-9*E_3+5*E_4},
      {-2*E_0+8*E_1-2*E_3+8*E_4, 4*E_0-9*E_1+4*E_3-9*E_4},
      {-8*E_0-9*E_1-9*E_2+5*E_3-7*E_4, 6*E_0+6*E_1+9*E_2-E_3-E_4}},
    matrix {{8*E_0+9*E_1+E_2, -9*E_0+3*E_1-7*E_2}, {-6*E_0+E_1-3*E_2,
      -3*E_0-5*E_1-8*E_2}, {-8*E_0+9*E_1-7*E_2-6*E_3+7*E_4,
      8*E_0+E_1+9*E_2+6*E_3-9*E_4}, {-2*E_0-5*E_1-7*E_2-9*E_3+2*E_4,
      -7*E_0+8*E_1-E_2-3*E_3+3*E_4}},
    matrix {{-9*E_0+2*E_1+3*E_2, -4*E_0+5*E_1+6*E_2}, {-8*E_0+3*E_2,
      -E_0+2*E_1-9*E_2}, {-3*E_0-4*E_1+7*E_2-3*E_3+3*E_4,
      7*E_0+4*E_1+5*E_2+7*E_3-6*E_4}, {E_0-9*E_1+E_2-4*E_3-3*E_4,
      -E_0-4*E_1+7*E_2+4*E_3-2*E_4}},
     matrix {{5*E_0+6*E_1-8*E_2, 8*E_0-4*E_1-8*E_2}, {E_0-3*E_1+6*E_2,
      -2*E_0-6*E_1-E_2}, {-5*E_0-2*E_1+3*E_2-9*E_3-6*E_4,
      5*E_0-5*E_2+9*E_3-9*E_4}, {-9*E_0+E_1+E_2-3*E_3+7*E_4,
      -E_0-7*E_1+7*E_2-4*E_3-E_4}}};
    adjData:={{(4, 12, 13), 7, (12, 24, 13), 3, (12, 19, 8), 9, (7, 7, 1)},
	{(4, 12, 13), 6, (12, 24, 13), 6, (12, 18, 7), 6, (6, 6, 1)},
	{(4, 12, 13), 5, (12, 24, 13), 9, (12, 17, 6), 3, (5, 5, 1)},
	{(4, 12, 13), 4, (12, 24, 13), 12, (12, 16, 5), 0, (4, 4, 1)},
	{(4, 12, 13), 8, (12, 24, 13), 1, (12, 20, 9), 8, (8, 9, 2)},
	{(4, 12, 13), 7, (12, 24, 13), 4, (12, 19, 8), 5, (7, 8, 2)},
	{(4, 12, 13), 6, (12, 24, 13), 7, (12, 18, 7), 2, (6, 7, 2)}
	};
    X:=aboRanestadSurfaceFromMatrix(P4,Ms_k);
    return (X,adjData_k);
    );
    if not member(char P4 ,{19}) then (
	<<" no example in characteristic = "<< char P4<<" recorded yet." <<endl);
    )

/// -* Test the list of examples of aboRanestad surfaces *-
restart
needsPackage"NongeneralTypeSurfacesInP4"
kk=ZZ/19;
P4=kk[x_0..x_4];
E=kk[e_0..e_4,SkewCommutative=>true]
(X,L0)=specificAboRanestadSurface(P4,E,0);
minimalBetti X
elapsedTime L=adjunctionProcess X;
L_0==L0,minimalBetti L_3

elapsedTime (X,L0)=specificAboRanestadSurface(P4,E,1);
minimalBetti X
elapsedTime L=adjunctionProcess X;
L_0
L_0==L0,minimalBetti L_3

elapsedTime (X,L0)=specificAboRanestadSurface(P4,E,2);
minimalBetti X
elapsedTime L=adjunctionProcess X;
L_0
L_0==L0,minimalBetti L_3

elapsedTime (X,L0)=specificAboRanestadSurface(P4,E,3);
minimalBetti X
elapsedTime L=adjunctionProcess X;
L_0
L_0==L0,minimalBetti L_3

elapsedTime (X,L0)=specificAboRanestadSurface(P4,E,4);
minimalBetti X
elapsedTime L=adjunctionProcess X;
L_0
L_0==L0,minimalBetti L_3

elapsedTime (X,L0)=specificAboRanestadSurface(P4,E,5);
minimalBetti X
elapsedTime L=adjunctionProcess X;
L_0
L_0==L0,minimalBetti L_3

elapsedTime (X,L0)=specificAboRanestadSurface(P4,E,6);
minimalBetti X
elapsedTime L=adjunctionProcess X;
L_0
L_0==L0,minimalBetti L_3


minimalBetti X
elapsedTime L=adjunctionProcess X;
L_0
L_0  ,minimalBetti L_3
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



      -* Abo surfaces *-

testMatrix1=method(Options=>{Verbose=>false,SingX=>true})
testMatrix1(Matrix,Ring) := opt -> (mE3x4,P4) -> (
    --toDo improve the code using a Hom computation of E-modules
    E:= ring mE3x4;
    kk:= coefficientRing P4;
    m1x3 := matrix{{E_0,E_1,E_2}};
    a:=symbol a;
    b:=symbol b;
    bs := flatten apply(3,i->flatten apply(3,j->b_(i,j)));
    as := flatten apply(1,i->flatten apply(4,j->a_(i,j)));
    B := kk[bs,as];
    ExB := E**B;
    E2 := sub(basis(2,E),ExB);
    a1x4 := matrix apply(1,i->apply(4,j->(sub(a_(i,j),ExB))));
    b3x3 := matrix apply(3,i->apply(3,j->(sub(b_(i,j),ExB))));
    E3 := sub(basis(3,E),ExB);
    m4x3 := transpose((transpose sub(m1x3,ExB)) | b3x3);
    m4x4 := (transpose a1x4) | (transpose sub(mE3x4,ExB));
    c := m4x4*m4x3;
    m13x12:=map(E^13,,sub(transpose diff(sub(vars B,ExB),transpose flatten c),E));
    rank source syz(m13x12,DegreeLimit=>3)
    --betti syz(m13x12,DegreeLimit=>3)
    )


testMatrix=method(Options=>{Verbose=>false,SingX=>true})
testMatrix(Matrix,Ring) := opt -> (mE3x4,P4) -> (
    E:= ring mE3x4;
    kk:= coefficientRing P4;
    m1x3 := matrix{{E_0,E_1,E_2}};
    a:=symbol a;
    b:=symbol b;
    bs := flatten apply(3,i->flatten apply(3,j->apply(10,k->b_(i,j,k))));
    as := flatten apply(1,i->flatten apply(4,j->apply(10,k->a_(i,j,k))));
    B := kk[bs,as];
    ExB := E**B;
    E2 := sub(basis(2,E),ExB);
    a1x4 := matrix apply(1,i->apply(4,j->sum(10,k->(sub(a_(i,j,k),ExB)*E2_(0,k)))));
    b3x3 := matrix apply(3,i->apply(3,j->sum(10,k->(sub(b_(i,j,k),ExB)*E2_(0,k)))));
    E3 := sub(basis(3,E),ExB);
    m4x3 := transpose((transpose sub(m1x3,ExB)) | b3x3);
    m4x4 := (transpose a1x4) | (transpose sub(mE3x4,ExB));
    c := m4x4*m4x3;
    Is := trim ideal sub(contract(E3,flatten c),B);
    if not opt.SingX then return betti Is;
    sol := vars B%Is;
    if opt.Verbose then << betti Is <<endl;
    F := null; beta := null; beta0 := null; alpha':=null;
    alpha0:=null;alpha:=null;delta:=null;I:=null;bb:=null;
    tau:=null;a1x4s:=null;m4x4s:=null;randSols:=null;
    while ( -- degree 12 surface
        randSols = sub(sol,random(kk^1,kk^130));
	a1x4s = sub(a1x4,vars E|randSols);
	m4x4s = (transpose a1x4s) | (transpose mE3x4);
	bb = map(E^4,,m4x4s);
	tau = syz bb;
	beta0 = bb;
	alpha' = submatrix(tau,,{0,1,2});
	alpha0 = alpha' | (sub(tau,E)*random(source sub(tau,E),E^{1:-4}));
	beta = beilinson(beta0,P4);
	alpha = beilinson(alpha0,P4);
	F = prune homology(beta,alpha);
	delta = syz transpose presentation F;
	I = ideal (delta);
    if opt.Verbose then <<"degree X == 12 and codim X == 2 is "<< degree I == 12 and codim I == 2 <<endl;
        not( degree I==12 and codim I ==2)) do ();
    saturate ideal singularLocus I)

testMatrix2=method(Options=>{Verbose=>false,WithM3x13 =>false,WithX=>false})
-- Input: m3x4 Matrix, linear matrix over the exterior algebra
--        P4 Ring, coordinate ring of P4
-- Output: d, ZZ, dimension of Hom(coker m3x4, coker m3x1**E^{1}
--         m3x13 Matrix, of 1-forms and 2 forms over the exterior algebra
--
testMatrix2(Matrix,Ring) := o -> (m3x4,P4) -> (
    E:=ring m3x4;
    m3x1:=matrix{{E_0},{E_1},{E_2}};
    if o.Verbose then (
	elapsedTime hom:=Hom(coker m3x4,coker m3x1**E^{2},DegreeLimit=>1)) else (
        betti(hom=Hom(coker m3x4,coker m3x1**E^{2},DegreeLimit=>1)));
    if hom==0 then r:=0 else (B:=betti hom;r=B#(0,{0},0));
    --r:=if member((0,{1},1),keys B) then B#(0,{1},1) else 0;
    if not (o.WithM3x13 or o.WithX) then return r;
    if r==0 then return (r,null);
    kk:=coefficientRing ring m3x4;
    c:=null;
    genHomo:=sum(r,i->(
	while (c=random kk; c==0) do ();c*hom_i));
    betti(m3x3:=homomorphism genHomo);
   
    m3x13:=map(E^{3:1},,(m3x1**E^{1}|matrix m3x3));
    if not degrees source m3x13 == {{0}, {1}, {1}, {1}} then return (r,null);
    if not o.WithX then return (r,m3x13);
    s1:=syz m3x13;
    if not degrees source s1 == {{2}, {2}, {2}, {2}, {3}, {3}, {3}, {3}, {3}} then return (r,null);
--betti m3x13,  source s1== E^{0,3:1}
    s2:=s1*((id_(E^{4:-2})||map(E^{5:-3},E^{4:-3},0))|random(source s1,E^{4:-3}));
    --betti s2
    T1:=res coker transpose s2;
    T2:=res(coker transpose T1.dd_6,LengthLimit=>8);
    X:=saturate ideal syz symExt(T2.dd_8,P4);
    dimDegSGCorrect:= dim X==3 and degree X==12 and sectionalGenus X ==13;
    if not dimDegSGCorrect then return (r,null);
    if o.Verbose then (
	elapsedTime dimSingX:=dim singularLocus(P4/X);
	<<"dim SingX = " <<dimSingX <<flush<<endl;);
    return (r,X)
    )
    
///

///




aboSurfaceFromMatrix= method(Options=>{Verbose=>false})
aboSurfaceFromMatrix(Matrix,Ring) := opt -> (mE3x4,P4) -> (
    E:= ring mE3x4;
    kk:= coefficientRing P4;
    m1x3 := matrix{{E_0,E_1,E_2}};
    a:=symbol a;
    b:=symbol b;
    bs := flatten apply(3,i->flatten apply(3,j->apply(10,k->b_(i,j,k))));
    as := flatten apply(1,i->flatten apply(4,j->apply(10,k->a_(i,j,k))));
    B := kk[bs,as];
    ExB := E**B;
    E2 := sub(basis(2,E),ExB);
    a1x4 := matrix apply(1,i->apply(4,j->sum(10,k->(sub(a_(i,j,k),ExB)*E2_(0,k)))));
    b3x3 := matrix apply(3,i->apply(3,j->sum(10,k->(sub(b_(i,j,k),ExB)*E2_(0,k)))));
    E3 := sub(basis(3,E),ExB);
    m4x3 := transpose((transpose sub(m1x3,ExB)) | b3x3);
    m4x4 := (transpose a1x4) | (transpose sub(mE3x4,ExB));
    c := m4x4*m4x3;
    Is := trim ideal sub(contract(E3,flatten c),B);
    assert(rank source gens Is<115);
    sol := vars B%Is;
    if opt.Verbose then << betti Is <<endl;
    randSols:=null;a1x4s:=null;m4x4s:=null;bb:=null;tau:=null;beta0:=null;
    alpha':=null;alpha0:=null;beta:=null;alpha:=null;F:=null;delta:=null;I:=null;cd:=null;
    while ( -- smooth surface
    while ( -- degree 12 surface
        randSols = sub(sol,random(kk^1,kk^130));
	a1x4s = sub(a1x4,vars E|randSols);
	m4x4s = (transpose a1x4s) | (transpose mE3x4);
	bb = map(E^4,,m4x4s);
	tau = syz bb;
	beta0 = bb;
	alpha' = submatrix(tau,,{0,1,2});
	alpha0 = alpha' | (sub(tau,E)*random(source sub(tau,E),E^{1:-4}));
	beta = beilinson(beta0,P4);
	alpha = beilinson(alpha0,P4);
	F = prune homology(beta,alpha);
	delta = syz transpose presentation F;
	I = ideal (delta);
    if opt.Verbose then <<"degree X == 12 and codim X == 2 is "<< degree I == 12 and codim I == 2 <<endl;
        not( degree I==12 and codim I ==2)) do ();
        cd=codim singularLocus I;
    if opt.Verbose then <<"codim singX = " << cd << endl;
       not (cd ==5) ) do ();
    I)

abo112224Or111234Surface=method(Options=>{Verbose=>false,Count=>false})
  ---finds Abo surfaces with canonical divisor (1,1,1,1,4,4) from (3x5) matrices over P3, s.t. the Bordiga surface is smooth and has seven rank two planes meeting the 1x3 line
abo112224Or111234Surface( Ring, Ring, ZZ):= opt -> (P4,P3,h) -> (
 kk := coefficientRing P4;
    e:= symbol e;
     P3xP4 := P3**P4;
    E := kk[e_0..e_4,SkewCommutative=>true];
    m1x3 := matrix{{e_0,e_1,e_2}};
       a:=symbol a;
    b:=symbol b;
    bs := flatten apply(3,i->flatten apply(3,j->apply(10,k->b_(i,j,k))));
    as := flatten apply(1,i->flatten apply(4,j->apply(10,k->a_(i,j,k))));
    B := kk[bs,as];
    ExB := E**B;
    E2 := sub(basis(2,E),ExB);
    a1x4 := matrix apply(1,i->apply(4,j->sum(10,k->(sub(a_(i,j,k),ExB)*E2_(0,k)))));
    b3x3 := matrix apply(3,i->apply(3,j->sum(10,k->(sub(b_(i,j,k),ExB)*E2_(0,k)))));
    E3 := sub(basis(3,E),ExB);
    m4x3 := transpose((transpose sub(m1x3,ExB)) | b3x3);
    count:=1;count1:=1;count2:=1;
    isSurface := false;
    ek1:= null;k31:=null;ek2:= null;k32:=null;ek3:= null;k33:=null;ek4:= null;k34:=null;
    m3x4:=null;m4x4:=null;c :=null;Is:=null;sol:=null;randsol:=null;a1x4s:=null;
    m4x4s:=null;bb:=null;tau:=null;beta0:=null;alpha':=null;alpha0:=null;
    beta:=null;alpha:=null;F:=null;delta:=null;I:=null;randSols:=null;rIs:=null;hdim:=null;
    m3x5:=null;
    while ( --get smooth surface
   -- count1=1;	
    while ( -- get surface of degree 12
	 -- count=1;
          while ( -- syz bb as desired
	      while (
		  --- A 3x5 matrix with 3x2 rigth submatrix of rank 1 along three lines in chain that contains at least 4 of the 3x5 matrix' rank 2 points, the middle line has three points where the 3x5 matrix has rank 2
--m3x5=random(P3^3,P3^2)*matrix{ {P3_0},{P3_1}}|random(P3^3,P3^2)*matrix{ {P3_0},{P3_3}}|random(P3^3,P3^{1:-1})|matrix{ {0,P3_0},{P3_1,0},{P3_2,P3_3}};
m3x5=transpose(transpose(random(P3^2,P3^3)*matrix{ {P3_0},{P3_2},{P3_3}})|matrix{ {0}})|random(P3^3,P3^3)*matrix{ {P3_0},{P3_2},{P3_3}}|random(P3^3,P3^2)*matrix{ {P3_1},{P3_2}}|matrix{ {0,P3_0},{P3_1,P3_2},{P3_2,P3_3}};
m3x4=sub(transpose (sub(diff(sub(vars P3,P3xP4),transpose (sub(vars P4,P3xP4)*sub(transpose m3x5,P3xP4))),P4)), vars E);
	      m4x4 = (transpose a1x4) | ( sub(m3x4,ExB));
	      c = m4x4*m4x3;
	      Is = trim ideal sub(contract(E3,flatten c),B);
	      rIs=rank source gens Is;
	      hdim=115-rIs;
	 not (hdim>=h)) do (count=count+1);
	      sol = vars B%Is;
	      randSols = sub(sol,random(kk^1,kk^130));
	      a1x4s = sub(a1x4,vars E|randSols);
	      m4x4s = (transpose a1x4s) | ( m3x4);
	      bb = map(E^4,,m4x4s);
	      tau = syz bb;
	  	      not ((tally degrees source tau)_{3} == 3 and 
		  (tally degrees source tau)_{4} == 5 )) do (count2=count2+1);
          beta0 = bb;
	  alpha' = submatrix(tau,,{0,1,2});
	  alpha0 = alpha' | (sub(tau,E)*random(source sub(tau,E),E^{1:-4}));
	  beta = beilinson(beta0,P4);
	  alpha = beilinson(alpha0,P4);
	  F = prune homology(beta,alpha);
	  delta = syz transpose presentation F;
	  I = ideal (delta);
          not (degree I == 12 and codim I == 2) )
      do (count1=count1+1);
       if opt.Verbose then << "count= " <<count << endl;
      if opt.Count then << "count1= " << count1 <<endl;
        singX:= singularLocus I; 
        not codim singX == 5) do ();
      --if opt.Count then << "count2= " << count2 <<endl;      
      (I, m3x4, hdim))


///-* Test abo112224Or111234AboSurface *-
restart
loadPackage "NongeneralTypeSurfacesInP4"

kk=ZZ/19;
P4=kk[x_0..x_4]
P3=kk[y_0..y_3]
P2=kk[z_0..z_2]
E= kk[e_0..e_4,SkewCommutative=>true];

h=2
--- Homs is 2-dimensional  (at least 5 rank two points of 3x5 matrix are rank one points of right 3x2 submatrix)
  setRandomSeed("get a 111234 surface in a minute");
elapsedTime (X,m3x4,r)=abo112224Or111234Surface(P4,P3,h,Verbose=>true,Count=>true);
minimalBetti X
r
partitionOfCanonicalDivisorOfAboSurface X == {1, 1, 1, 2, 3, 4}
-- Residual in quintics is five 6-secant lines and a 11-secant conic
  setRandomSeed("get a 112224 surface in a minute");
elapsedTime (X,m3x4,r)=abo112224Or111234Surface(P4,P3,h,Verbose=>true,Count=>true);
minimalBetti X
r
partitionOfCanonicalDivisorOfAboSurface X == {1, 1, 2, 2, 2, 4}
///

abo111144Surface=method(Options=>{Verbose=>false,Count=>false})
  ---finds Abo surfaces with canonical divisor (1,1,1,1,4,4) from special (3x5) matrices over P3, s.t. the Bordiga surface is smooth and has seven rank two planes meeting the 1x3 line
abo111144Surface( Ring, Ring):= opt -> (P4,P3) -> (
 kk := coefficientRing P4;
    e:= symbol e;
     P3xP4 := P3**P4;
    E := kk[e_0..e_4,SkewCommutative=>true];
    m1x3 := matrix{{e_0,e_1,e_2}};
       a:=symbol a;
    b:=symbol b;
    bs := flatten apply(3,i->flatten apply(3,j->apply(10,k->b_(i,j,k))));
    as := flatten apply(1,i->flatten apply(4,j->apply(10,k->a_(i,j,k))));
    B := kk[bs,as];
    ExB := E**B;
    E2 := sub(basis(2,E),ExB);
    a1x4 := matrix apply(1,i->apply(4,j->sum(10,k->(sub(a_(i,j,k),ExB)*E2_(0,k)))));
    b3x3 := matrix apply(3,i->apply(3,j->sum(10,k->(sub(b_(i,j,k),ExB)*E2_(0,k)))));
    E3 := sub(basis(3,E),ExB);
    m4x3 := transpose((transpose sub(m1x3,ExB)) | b3x3);
    count:=1;count1:=1;count2:=1;
    isSurface := false;
    ek1:= null;k31:=null;ek2:= null;k32:=null;ek3:= null;k33:=null;ek4:= null;k34:=null;
    m3x4:=null;m4x4:=null;c :=null;Is:=null;sol:=null;randsol:=null;a1x4s:=null;
    m4x4s:=null;bb:=null;tau:=null;beta0:=null;alpha':=null;alpha0:=null;
    beta:=null;alpha:=null;F:=null;delta:=null;I:=null;randSols:=null;rIs:=null;
    hdim:=null;m3x5:=null;
    while ( --get smooth surface
   -- count1=1;	
    while ( -- get surface of degree 12
	 -- count=1;
          while ( -- syz bb as desired
          --m3x5=transpose(matrix{{P3_0}+{P3_3}}|random(P3^1,P3^{2:-1}))|random(P3^3,P3^2)*matrix{{P3_2},{P3_3}}|random(P3^3,P3^2)*matrix{{P3_0},{P3_1}}|matrix{ {0,P3_2},{P3_0,0},{-P3_1,-P3_3}};
              m3x5=transpose(matrix{{P3_1}+{P3_3}}|random(P3^1,P3^{2:-1}))|transpose(matrix{{P3_2}}|transpose(random(P3^2,P3^2)*matrix{{P3_2},{P3_3}}))|transpose(matrix{{P3_0}}|transpose(random(P3^2,P3^2)*matrix{{P3_0},{P3_1}}))|matrix{ {0,P3_2},{P3_0,0},{-P3_1,-P3_3}};
              m3x4=sub(transpose (sub(diff(sub(vars P3,P3xP4),transpose (sub(vars P4,P3xP4)*sub(transpose m3x5,P3xP4))),P4)), vars E);
	      m4x4 = (transpose a1x4) | ( sub(m3x4,ExB));
	      c = m4x4*m4x3;
	      Is = trim ideal sub(contract(E3,flatten c),B);
	      rIs=rank source gens Is;
	      hdim=115-rIs;
	      sol = vars B%Is;
	      randSols = sub(sol,random(kk^1,kk^130));
	      a1x4s = sub(a1x4,vars E|randSols);
	      m4x4s = (transpose a1x4s) | ( m3x4);
	      bb = map(E^4,,m4x4s);
	      tau = syz bb;
	      not ((tally degrees source tau)_{3} == 3 and 
		  (tally degrees source tau)_{4} == 5 )) do (count=count+1);
          beta0 = bb;
	  alpha' = submatrix(tau,,{0,1,2});
	  alpha0 = alpha' | (sub(tau,E)*random(source sub(tau,E),E^{1:-4}));
	  beta = beilinson(beta0,P4);
	  alpha = beilinson(alpha0,P4);
	  F = prune homology(beta,alpha);
	  delta = syz transpose presentation F;
	  I = ideal (delta);
          not (degree I == 12 and codim I == 2) )
      do (count1=count1+1);
      if opt.Verbose then << "count= " <<count << endl;
      if opt.Count then << "count1= " << count1 <<endl;
      singX:= singularLocus I; 
      not codim singX == 5) do (count2=count2+1);
      if opt.Count then << "count2= " << count2 <<endl;      
      (I, m3x4, hdim))

/// -* test abo111144Surface *-
  kk=ZZ/nextPrime(10^3)
P4=kk[x_0..x_4]
P3=kk[y_0..y_3]
P2=kk[z_0..z_2]
E= kk[e_0..e_4,SkewCommutative=>true];
  setRandomSeed("quitefastest");
  elapsedTime (X,m3x4,r)=abo111144Surface(P4,P3,Verbose=>true,Count=>true);
  minimalBetti X
  r
  partitionOfCanonicalDivisorOfAboSurface X
///


abo111333Surface=method(Options=>{Verbose=>false})
abo111333Surface(Ring,Ring) := opt -> (P4,E) -> (
    kk:=coefficientRing P4;
    u:= symbol u;
    P1:=kk[u_0..u_1];
    z:= symbol z;
    P2:=kk[z_0..z_2];
    y:=symbol y;
    P3:=kk[y_0..y_3];
    P3xP4:=P3**P4;
    tenPtsInP2:=intersect apply(10,i->ideal random(P2^1,P2^{2:-1}));
    fP2:=res tenPtsInP2;
    m4x5:=map(P2^4,,transpose (fP2.dd_2));
    bordiga:=ker map(P2,P4,fP2.dd_1);
    fP4:=res bordiga;
    m3x4:=map(P4^3,,transpose fP4.dd_2);
    m3x5 := map(P3^3,,sub(diff(sub(vars P4,P3xP4),sub(m3x4,P3xP4)*sub(transpose vars P3,P3xP4)),P3));
    tenPtsInP3 := minors(3,m3x5); 
    tenPtsInP3List:=decompose tenPtsInP3;
    m2x3:=map(P3^2,,transpose ((res intersect (tenPtsInP3List_{0..5})).dd_3^{2..4}));
    P1xP3:=P1**P3;
    paraCubic:=map(P1^1,,transpose syz transpose sub(diff(sub(transpose vars P3,P1xP3),
		sub(vars P1,P1xP3)*sub(m2x3,P1xP3)),P1));
    if opt.Verbose then <<betti syz sub(m3x5,paraCubic)<<endl;
    twoColumns:=sub(diff(vars P1,(syz sub(m3x5,paraCubic))_{0}),kk);
    m3x2:=m3x5*twoColumns;
    assert(minors(2,m3x2)==minors(2,m2x3));
    --=> column 2x3  twisted cubic found
    coordinateChange:=(random(kk^5,kk^3)|twoColumns);
    assert(det coordinateChange!=0);
    coordinateChange1:=vars P4*transpose coordinateChange;
    mE3x4:=sub(sub(m3x4,coordinateChange1),vars E);
    if opt.Verbose then <<adjointMatrices(mE3x4,P2,P3,P4)<<endl;
    X:=aboSurfaceFromMatrix(mE3x4,P4,Verbose=>opt.Verbose);
    (X,mE3x4))

///
kk=ZZ/nextPrime 10^3
P4=kk[x_0..x_4]
E=kk[e_0..e_4,SkewCommutative=>true];
elapsedTime (X,m3x4)=abo111333Surface(P4,E);
elapsedTime K=partitionOfCanonicalDivisorOfAboSurface X
R=residualInQuintics X;
cR=primaryDecomposition R;
tally apply(cR,c->((dim c, degree c),(dim(c+X),degree(c+X))))
testMatrix1(m3x4,P4)
testMatrix2(m3x4,P4)
X1=aboSurfaceFromMatrix(m3x4,P4);

K=partitionOfCanonicalDivisorOfAboSurface(X,Equations=>true);
betti K
K1=partitionOfCanonicalDivisorOfAboSurface(X1,Equations=>true);
K==K1
X==X1
betti tateResolutionOfSurface X
///


abo111117Surface=method(Options=>{Verbose=>false})


abo111117Surface(Ring,Ring) := o -> (P4,E) -> (
    kk:=coefficientRing P4;
    z:=symbol z;
    P3:=kk[z_0..z_3];
    P3xP4:=P3**P4;
    --a 3x2 matrix that has rank one along three lines L1,L2,L3 and rank 0 at the point (0:1:0:0) in P3
    n3x2:=random(kk^3,kk^3)*matrix {{ z_0, 0}, { 0, z_2},{ z_3, z_3}}*random(kk^2,kk^2);
    --Ls:=decompose minors(2,n3x2);
    gm1:=random(kk^3,kk^3)*matrix {{ 0}, { 0},{ 0}}| random(kk^3,kk^3)*matrix {{ z_0, 0}, { 0, z_2},{ z_3, z_3}}*random(kk^2,kk^2);
    gm2:=matrix{{z_1,z_1,z_1},{z_1,z_1,z_1},{z_1,z_1,z_1}};
    -- a 3x3 matrix of rank one at the point (0:1:0:0) and
    -- at the three points of intersection between L1,L2,L3 and the plane z_3=0:
    gm:=transpose (gm1+gm2);
    -- a 3x5 matrix with rank one at (0:1:0:0) and rank two
    -- at the three points of intersection between L1,L2,L3 and the plane z_3=0
    n3x5 := gm |n3x2;
    n33:=minors(3,n3x5);
    n32:=minors(2,n3x2);
    --(degree n33, codim n33)--n3x5 has rank 2 in a scheme of length ten
    --degree (n33+n32), codim (n33+n32)--n3x5 has rank 2 in a scheme of length seven on the union of L1,L2,L3
    --primaryDecomposition n33
    xs:=vars P4;
    mn31:=sub(n3x5, P3xP4)*transpose(sub(xs,P3xP4));
    m3x4:=sub(diff(sub(vars P3,P3xP4),mn31),P4);
    --the 3x4 matrix adjoint to n3x5
    --decompose(minors(3,m3x4)):  the union of a cubic surface in a P3 and a cubic scroll
    mE3x4:=sub(m3x4,vars E);
    X:= if o.Verbose then elapsedTime aboSurfaceFromMatrix(mE3x4,P4) else (
	aboSurfaceFromMatrix(mE3x4,P4));
    assert((3,12,13)==(dim X,degree X,sectionalGenus X));
    (X,mE3x4)
    )


///
kk=ZZ/nextPrime 10^3
P4=kk[x_0..x_4]
E=kk[e_0..e_4,SkewCommutative=>true];
elapsedTime (X,m3x4)=abo111117Surface(P4,E);
elapsedTime K=partitionOfCanonicalDivisorOfAboSurface X
R=residualInQuintics X;
cR=primaryDecomposition R;
tally apply(cR,c->((dim c, degree c),(dim(c+X),degree(c+X))))
testMatrix1(m3x4,P4)
X1=aboSurfaceFromMatrix(m3x4,P4);

K=partitionOfCanonicalDivisorOfAboSurface(X,Equations=>true);
betti K
K1=partitionOfCanonicalDivisorOfAboSurface(X1,Equations=>true);
K==K1
betti(T=tateResolutionOfSurface X)
betti(m3x31=(T.dd_4)^{0..2})
betti(T1=res coker m3x31)
E'=ring T1
betti(m13x44=T1.dd_2*random(T1_2,E'^{4:-4,4:-5}))
betti(T2=res coker transpose m13x44)
betti(T3=res coker transpose T2.dd_3)
X2=saturate ideal syz symExt(T3.dd_5,P4);
K2=partitionOfCanonicalDivisorOfAboSurface(X2,Equations=>true);
K==K2
X==X2
///



adjointMatrices=method(Options=>{Verbose=>false})
adjointMatrices(Matrix,Ring,Ring,Ring):= opt -> (mE3x4,P2,P3,P4) -> (
    m3x4:=sub(mE3x4,vars P4);
    line:=ideal (vars P4)_{0..2};
    betti syz (m3x4%line);
    apply(4,i-> trim ideal ((m3x4%line)_{i}));    
    P2xP4:= P2**P4;
    m4x5:=map(P2^4,,sub(diff(sub(vars P4,P2xP4),transpose (sub(vars P2,P2xP4)*sub(m3x4,P2xP4))),P2));
    P3xP4:= P3**P4;
    -*
    betti (F=res ideal ((sub(m3x4,P3xP4)*sub(transpose vars P3,P3xP4))%sub(line,P3xP4)))
    F.dd_3
    betti res saturate(ideal ((sub(m3x4,P3xP4)*sub(transpose vars P3,P3xP4))%sub(line,P3xP4)),sub(ideal(x_3,x_4),P3xP4))
   
    betti res coker transpose F.dd_3
    *-
    m3x5 :=map(P3^3,,sub(diff(sub(vars P4,P3xP4),sub(m3x4,P3xP4)*sub(transpose vars P3,P3xP4)),P3));
    m2x3 :=map(P3^2,,transpose sub(diff(sub((vars P4)_{3,4},P3xP4),sub(m3x4,P3xP4)*sub(transpose vars P3,P3xP4)),P3));
    --<< betti m2x3 <<betti m3x4 << betti m4x5;
    --if opt.Verbose then
    bordiga:=minors(3,m3x4);singB:=singularLocus bordiga;
    (codim singB, degree singB,betti saturate (minors(3,m3x4)+ideal(P4_0,P4_1,P4_2)),
    tally apply(primaryDecomposition minors(3,m3x5),c->degree c),
    tally apply( primaryDecomposition minors(4,m4x5),c->degree c),
    degree (minors(3,m3x5)+minors(2,m2x3)),
    tally apply(primaryDecomposition (minors(3,m3x5)+minors(2,m2x3)),c->(dim c, degree c)))
      )


///
mKs={}
kk=ZZ/19;
P4=kk[x_0..x_4]
E=kk[e_0..e_4,SkewCommutative=>true]
 (X,m3x4)=randomAboSurface(P4,E,Verbose=>false);
elapsedTime mKs'=collectAboSurfaces(mKs,P4,E,2);#mKs'
///

///
kk=ZZ/nextPrime 10^4
P4=kk[x_0..x_4]
E=kk[e_0..e_4,SkewCommutative=>true]
elapsedTime X=abo111333Surface(P4,E);
analyzeAboSurface X
///
randomAboSurfaceWithLargeHomSpace=method(Options=>{Verbose=>false,Count=>false})
randomAboSurfaceWithLargeHomSpace(Ring,Ring,ZZ) := opt -> (P4,E,h) -> (
    assert(char P4==char E);
    kk:=coefficientRing E;
    y:= symbol y;z:=symbol z;
    P2:=kk[y_0..y_2];
    P3:=kk[z_0..z_3];    
    r:=null;
    while (r=random(kk);member(r, {1_kk,0_kk})) do ();
    m1x3 := matrix{{E_0,E_1,E_2}};
    p1 := matrix{{E_0,E_1,E_2,E_3}};
    p2 := matrix{{E_0,E_1,E_2,E_4}};
    p3 := matrix{{E_0,E_1,E_2,E_4-random(kk)*E_3}};
    p4 := matrix{{E_0,E_1,E_2,E_4-E_3}};
    a:=symbol a;
    b:=symbol b;
    bs := flatten apply(3,i->flatten apply(3,j->apply(10,k->b_(i,j,k))));
    as := flatten apply(1,i->flatten apply(4,j->apply(10,k->a_(i,j,k))));
    B := kk[bs,as];
    ExB := E**B;
    E2 := sub(basis(2,E),ExB);
    a1x4 := matrix apply(1,i->apply(4,j->sum(10,k->(sub(a_(i,j,k),ExB)*E2_(0,k)))));
    b3x3 := matrix apply(3,i->apply(3,j->sum(10,k->(sub(b_(i,j,k),ExB)*E2_(0,k)))));
    E3 := sub(basis(3,E),ExB);
    m4x3 := transpose((transpose sub(m1x3,ExB)) | b3x3);
    count:=1;count1:=1;count2:=1;
    isSurface := false;
    ek1:= null;k31:=null;ek2:= null;k32:=null;ek3:= null;k33:=null;ek4:= null;k34:=null;
    m3x4:=null;m4x4:=null;c :=null;Is:=null;sol:=null;randsol:=null;a1x4s:=null;
    m4x4s:=null;bb:=null;tau:=null;beta0:=null;alpha':=null;alpha0:=null;
    beta:=null;alpha:=null;F:=null;delta:=null;I:=null;randSols:=null;rIs:=null;dHom:=null;
    while ( --get smooth surface
    count1=1;	
    while ( -- get surface of degree 12
	  count=1;
          while ( -- syz bb as desired
	      while ( -- large hom space
	      ek1 = random(E^2,E^4)*transpose p1;
	      k31 = random(E^3,E^2)*ek1;
	      ek2 = random(E^2,E^4)*transpose p2;
	      k32 = random(E^3,E^2)*ek2;
	      ek3 = random(E^2,E^4)*transpose p3;
	      k33 = random(E^3,E^2)*ek3;
	      ek4 = random(E^2,E^4)*transpose p4;
	      k34 = random(E^3,E^2)*ek4;
	      m3x4 = k31|k32|k33|k34;
	      if opt.PrintConstructionData then << (adjointMatrices(m3x4,P2,P3,P4)) <<endl;
	      m4x4 = (transpose a1x4) | (transpose sub(m3x4,ExB));
	      c = m4x4*m4x3;
	      Is = trim ideal sub(contract(E3,flatten c),B);
	      rIs=rank source gens Is;
	      dHom =115-rIs;
	      dHom<h) do ();
	      if opt.PrintConstructionData and opt.Verbose then (
		  <<"betti Is= " << betti Is <<endl);
	      sol = vars B%Is;
	      randSols = sub(sol,random(kk^1,kk^130));
	      a1x4s = sub(a1x4,vars E|randSols);
	      m4x4s = (transpose a1x4s) | (transpose m3x4);
	      bb = map(E^4,,m4x4s);
	      tau = syz bb;
	      if opt.PrintConstructionData and opt.Verbose then (
		  <<"betti syz bb = " << betti tau <<endl);
	      not ((tally degrees source tau)_{3} == 3 and 
		  (tally degrees source tau)_{4} == 5 )) do count=count+1;
	  if opt.Verbose then << "count= " <<count << endl;
          beta0 = bb;
	  alpha' = submatrix(tau,,{0,1,2});
	  alpha0 = alpha' | (sub(tau,E)*random(source sub(tau,E),E^{1:-4}));
	  beta = beilinson(beta0,P4);
	  alpha = beilinson(alpha0,P4);
	  F = prune homology(beta,alpha);
	  delta = syz transpose presentation F;
	  I = ideal (delta);
          not (degree I == 12 and codim I == 2) )
      do (count1=count1+1);
      if opt.Count then << "count1= " << count1 <<endl;
      if opt.PrintConstructionData then (
	      <<"betti Is= " << betti Is <<endl);
	     -- <<"betti syz bb = " << betti tau <<endl);
      singX:= singularLocus I; 
      if opt.PrintConstructionData then (
	  <<"codim singX = " << codim singX <<endl);
      not codim singX == 5) do (count2=count2+1);
      if opt.Count then << "count2= " << count2 <<endl;      
      (I,m3x4,dHom))

/// -*test randomAboSurfaceWithLargeHomSpace *-
needsPackage"NongeneralTypeSurfacesInP4"
kk=ZZ/19;
P4=kk[x_0..x_4];
E=kk[e_0..e_4,SkewCommutative=>true]
--elapsedTime (X,m3x4)=randomAboSurface(P4,E);--,PrintConstructionData=>true);
h=2
elapsedTime (X,m3x4,dh)=randomAboSurfaceWithLargeHomSpace(P4,E,h);
dh
partitionOfCanonicalDivisorOfAboSurface X
tally apply(decompose residualInQuintics X,c->(dim c -1 , degree c, genus c,(dim(c+X)-1, degree (c+X))))

///

randomAboSurfaceWithHomSpaceOfGivenDimension=method(Options=>
    {Verbose=>false,Count=>false})
randomAboSurfaceWithHomSpaceOfGivenDimension(Ring,Ring,ZZ) := opt -> (P4,E,h) -> (
    assert(char P4==char E);
    kk:=coefficientRing E;
    y:= symbol y;z:=symbol z;
    P2:=kk[y_0..y_2];
    P3:=kk[z_0..z_3];    
    r:=null;
    while (r=random(kk);member(r, {1_kk,0_kk})) do ();
    m1x3 := matrix{{E_0,E_1,E_2}};
    p1 := matrix{{E_0,E_1,E_2,E_3}};
    p2 := matrix{{E_0,E_1,E_2,E_4}};
    p3 := matrix{{E_0,E_1,E_2,E_4-random(kk)*E_3}};
    p4 := matrix{{E_0,E_1,E_2,E_4-E_3}};
    a:=symbol a;
    b:=symbol b;
    bs := flatten apply(3,i->flatten apply(3,j->apply(10,k->b_(i,j,k))));
    as := flatten apply(1,i->flatten apply(4,j->apply(10,k->a_(i,j,k))));
    B := kk[bs,as];
    ExB := E**B;
    E2 := sub(basis(2,E),ExB);
    a1x4 := matrix apply(1,i->apply(4,j->sum(10,k->(sub(a_(i,j,k),ExB)*E2_(0,k)))));
    b3x3 := matrix apply(3,i->apply(3,j->sum(10,k->(sub(b_(i,j,k),ExB)*E2_(0,k)))));
    E3 := sub(basis(3,E),ExB);
    m4x3 := transpose((transpose sub(m1x3,ExB)) | b3x3);
    count:=1;count1:=1;count2:=1;
    isSurface := false;
    ek1:= null;k31:=null;ek2:= null;k32:=null;ek3:= null;k33:=null;ek4:= null;k34:=null;
    m3x4:=null;m4x4:=null;c :=null;Is:=null;sol:=null;randsol:=null;a1x4s:=null;
    m4x4s:=null;bb:=null;tau:=null;beta0:=null;alpha':=null;alpha0:=null;
    beta:=null;alpha:=null;F:=null;delta:=null;I:=null;randSols:=null;rIs:=null;dHom:=null;
    while ( --get smooth surface
    count1=1;	
    while ( -- get surface of degree 12
	  count=1;
          while ( -- syz bb as desired
	      while ( -- large hom space
	      ek1 = random(E^2,E^4)*transpose p1;
	      k31 = random(E^3,E^2)*ek1;
	      ek2 = random(E^2,E^4)*transpose p2;
	      k32 = random(E^3,E^2)*ek2;
	      ek3 = random(E^2,E^4)*transpose p3;
	      k33 = random(E^3,E^2)*ek3;
	      ek4 = random(E^2,E^4)*transpose p4;
	      k34 = random(E^3,E^2)*ek4;
	      m3x4 = k31|k32|k33|k34;
	      m4x4 = (transpose a1x4) | (transpose sub(m3x4,ExB));
	      c = m4x4*m4x3;
	      Is = trim ideal sub(contract(E3,flatten c),B);
	      rIs=rank source gens Is;
	      dHom =115-rIs;
	      dHom=!=h) do ();
	      if opt.Verbose then (
		  <<"betti Is= " << betti Is <<endl);
	      sol = vars B%Is;
	      randSols = sub(sol,random(kk^1,kk^130));
	      a1x4s = sub(a1x4,vars E|randSols);
	      m4x4s = (transpose a1x4s) | (transpose m3x4);
	      bb = map(E^4,,m4x4s);
	      tau = syz bb;
	      not ((tally degrees source tau)_{3} == 3 and 
		  (tally degrees source tau)_{4} == 5 )) do count=count+1;
	  if opt.Verbose then << "count= " <<count << endl;
          beta0 = bb;
	  alpha' = submatrix(tau,,{0,1,2});
	  alpha0 = alpha' | (sub(tau,E)*random(source sub(tau,E),E^{1:-4}));
	  beta = beilinson(beta0,P4);
	  alpha = beilinson(alpha0,P4);
	  F = prune homology(beta,alpha);
	  delta = syz transpose presentation F;
	  I = ideal (delta);
          not (degree I == 12 and codim I == 2) )
      do (count1=count1+1);
      if opt.Count then << "count1= " << count1 <<endl;
           singX:= singularLocus I; 
      not codim singX == 5) do (count2=count2+1);
      if opt.Count then << "count2= " << count2 <<endl;      
      (I,m3x4,dHom))

/// -*test randomAboSurfaceWithLargeHomSpace *-
needsPackage"NongeneralTypeSurfacesInP4"
kk=ZZ/19;
P4=kk[x_0..x_4];
E=kk[e_0..e_4,SkewCommutative=>true]
--elapsedTime (X,m3x4)=randomAboSurface(P4,E);--,PrintConstructionData=>true);
h=3
elapsedTime (X,m3x4,dh)=randomAboSurfaceWithHomSpaceOfGivenDimension(P4,E,h);
dh
partitionOfCanonicalDivisorOfAboSurface X
tally apply(decompose residualInQuintics X,c->(dim c -1 , degree c, genus c,(dim(c+X)-1, degree (c+X))))

///


randomAboSurface=method(Options=>{Verbose=>false,Count=>false,
	PrintConstructionData=>false})

randomAboSurface(Ring,Ring) := opt -> (P4,E) -> (
    assert(char P4==char E);
    kk:=coefficientRing E;
    y:= symbol y;z:=symbol z;
    P2:=kk[y_0..y_2];
    P3:=kk[z_0..z_3];    
    r:=null;
    while (r=random(kk);member(r, {1_kk,0_kk})) do ();
    m1x3 := matrix{{E_0,E_1,E_2}};
    p1 := matrix{{E_0,E_1,E_2,E_3}};
    p2 := matrix{{E_0,E_1,E_2,E_4}};
    p3 := matrix{{E_0,E_1,E_2,E_4-random(kk)*E_3}};
    p4 := matrix{{E_0,E_1,E_2,E_4-E_3}};
    a:=symbol a;
    b:=symbol b;
    bs := flatten apply(3,i->flatten apply(3,j->apply(10,k->b_(i,j,k))));
    as := flatten apply(1,i->flatten apply(4,j->apply(10,k->a_(i,j,k))));
    B := kk[bs,as];
    ExB := E**B;
    E2 := sub(basis(2,E),ExB);
    a1x4 := matrix apply(1,i->apply(4,j->sum(10,k->(sub(a_(i,j,k),ExB)*E2_(0,k)))));
    b3x3 := matrix apply(3,i->apply(3,j->sum(10,k->(sub(b_(i,j,k),ExB)*E2_(0,k)))));
    E3 := sub(basis(3,E),ExB);
    m4x3 := transpose((transpose sub(m1x3,ExB)) | b3x3);
    count:=1;count1:=1;count2:=1;
    isSurface := false;
    ek1:= null;k31:=null;ek2:= null;k32:=null;ek3:= null;k33:=null;ek4:= null;k34:=null;
    m3x4:=null;m4x4:=null;c :=null;Is:=null;sol:=null;randsol:=null;a1x4s:=null;
    m4x4s:=null;bb:=null;tau:=null;beta0:=null;alpha':=null;alpha0:=null;
    beta:=null;alpha:=null;F:=null;delta:=null;I:=null;randSols:=null;dHom:=null;rIs:=null;
    while ( --get smooth surface
    count1=1;	
    while ( -- get surface of degree 12
	  count=1;
          while ( -- syz bb as desired
	      while ( -- enough hom
	      ek1 = random(E^2,E^4)*transpose p1;
	      k31 = random(E^3,E^2)*ek1;
	      ek2 = random(E^2,E^4)*transpose p2;
	      k32 = random(E^3,E^2)*ek2;
	      ek3 = random(E^2,E^4)*transpose p3;
	      k33 = random(E^3,E^2)*ek3;
	      ek4 = random(E^2,E^4)*transpose p4;
	      k34 = random(E^3,E^2)*ek4;
	      m3x4 = k31|k32|k33|k34;
	      if opt.PrintConstructionData then << (adjointMatrices(m3x4,P2,P3,P4)) <<endl;
	      m4x4 = (transpose a1x4) | (transpose sub(m3x4,ExB));
	      c = m4x4*m4x3;
	      Is = trim ideal sub(contract(E3,flatten c),B);
	      rIs=rank source gens Is;
	      dHom =115-rIs;
	      dHom<1) do ();
	      if opt.Verbose then (
		  <<"betti Is= " << betti Is <<endl);
	      sol = vars B%Is;
	      randSols = sub(sol,random(kk^1,kk^130));
	      a1x4s = sub(a1x4,vars E|randSols);
	      m4x4s = (transpose a1x4s) | (transpose m3x4);
	      bb = map(E^4,,m4x4s);
	      tau = syz bb;
	      if opt.Verbose then (
		  <<"betti syz bb = " << betti tau <<endl);
	      not ((tally degrees source tau)_{3} == 3 and 
		  (tally degrees source tau)_{4} == 5 )) do count=count+1;
	  if opt.Verbose then << "count= " <<count << endl;
          beta0 = bb;
	  alpha' = submatrix(tau,,{0,1,2});
	  alpha0 = alpha' | (sub(tau,E)*random(source sub(tau,E),E^{1:-4}));
	  beta = beilinson(beta0,P4);
	  alpha = beilinson(alpha0,P4);
	  F = prune homology(beta,alpha);
	  delta = syz transpose presentation F;
	  I = ideal (delta);
          not (degree I == 12 and codim I == 2) )
      do (count1=count1+1);
      if opt.Count then << "count1= " << count1 <<endl;
      singX:= singularLocus I; 
      not codim singX == 5) do (count2=count2+1);
      if opt.Count then << "count2= " << count2 <<endl;      
      (I,m3x4))

    

-*
randomAboSurface(Ring):= opt -> P4 -> (
    kk := coefficientRing P4;
    e:= symbol e;
    E := kk[e_0..e_4,SkewCommutative=>true];
    m1x3 := matrix{{e_0,e_1,e_2}};
    p1 := matrix{{e_0,e_1,e_2,e_3}};
    p2 := matrix{{e_0,e_1,e_2,e_4}};
    p3 := matrix{{e_0,e_1,e_2,e_4+e_3}};
    p4 := matrix{{e_0,e_1,e_2,e_4-e_3}};
    a:=symbol a;
    b:=symbol b;
    bs := flatten apply(3,i->flatten apply(3,j->apply(10,k->b_(i,j,k))));
    as := flatten apply(1,i->flatten apply(4,j->apply(10,k->a_(i,j,k))));
    B := kk[bs,as];
    ExB := E**B;
    E2 := sub(basis(2,E),ExB);
    a1x4 := matrix apply(1,i->apply(4,j->sum(10,k->(sub(a_(i,j,k),ExB)*E2_(0,k)))));
    b3x3 := matrix apply(3,i->apply(3,j->sum(10,k->(sub(b_(i,j,k),ExB)*E2_(0,k)))));
    E3 := sub(basis(3,E),ExB);
    m4x3 := transpose((transpose sub(m1x3,ExB)) | b3x3);
    count:=1;count1:=1;count2:=1;
    isSurface := false;
    ek1:= null;k31:=null;ek2:= null;k32:=null;ek3:= null;k33:=null;ek4:= null;k34:=null;
    m3x4:=null;m4x4:=null;c :=null;Is:=null;sol:=null;randsol:=null;a1x4s:=null;
    m4x4s:=null;bb:=null;tau:=null;beta0:=null;alpha':=null;alpha0:=null;
    beta:=null;alpha:=null;F:=null;delta:=null;I:=null;randSols:=null;
    while ( --get smooth surface
    count1=1;	
    while ( -- get surface of degree 12
	  count=1;
          while ( -- syz bb as desired
	      ek1 = random(E^2,E^4)*transpose p1;
	      k31 = random(E^3,E^2)*ek1;
	      ek2 = random(E^2,E^4)*transpose p2;
	      k32 = random(E^3,E^2)*ek2;
	      ek3 = random(E^2,E^4)*transpose p3;
	      k33 = random(E^3,E^2)*ek3;
	      ek4 = random(E^2,E^4)*transpose p4;
	      k34 = random(E^3,E^2)*ek4;
	      m3x4 = k31|k32|k33|k34;
	      m4x4 = (transpose a1x4) | (transpose sub(m3x4,ExB));
	      c = m4x4*m4x3;
	      Is = trim ideal sub(contract(E3,flatten c),B);
	      if opt.PrintConstructionData and opt.Verbose then (
		  <<"betti Is= " << betti Is <<endl);
	      sol = vars B%Is;
	      randSols = sub(sol,random(kk^1,kk^130));
	      a1x4s = sub(a1x4,vars E|randSols);
	      m4x4s = (transpose a1x4s) | (transpose m3x4);
	      bb = map(E^4,,m4x4s);
	      tau = syz bb;
	      if opt.PrintConstructionData and opt.Verbose then (
		  <<"betti syz bb = " << betti tau <<endl);
	      not ((tally degrees source tau)_{3} == 3 and 
		  (tally degrees source tau)_{4} == 5 )) do count=count+1;
	  if opt.Verbose then << "count= " <<count << endl;
          beta0 = bb;
	  alpha' = submatrix(tau,,{0,1,2});
	  alpha0 = alpha' | (sub(tau,E)*random(source sub(tau,E),E^{1:-4}));
	  beta = beilinson(beta0,P4);
	  alpha = beilinson(alpha0,P4);
	  F = prune homology(beta,alpha);
	  delta = syz transpose presentation F;
	  I = ideal (delta);
          not (degree I == 12 and codim I == 2) )
      do (count1=count1+1);
      if opt.Count then << "count1= " << count1 <<endl;
      if opt.PrintConstructionData then (
	      <<"betti Is= " << betti Is <<endl);
	     -- <<"betti syz bb = " << betti tau <<endl);
      singX:= singularLocus I; 
      if opt.PrintConstructionData then (
	  <<"codim singX = " << codim singX <<endl);
      not codim singX == 5) do (count2=count2+1);
      if opt.Count then << "count2= " << count2 <<endl;      
      I)
*-


randomEllipticAboSurface=method(Options=>{Verbose=>false,Count=>false,
	PrintConstructionData=>false,NumberOfRank1Points=>3})
randomEllipticAboSurface(Ring,Ring) := o -> (P4,P3) -> (
    if o.NumberOfRank1Points==1 then return randomEllipticAboSurface1(P4,P3);
    if o.NumberOfRank1Points==2 then return randomEllipticAboSurface2(P4,P3);
    if o.NumberOfRank1Points==3 then return randomEllipticAboSurface3(P4,P3);
    return null) 	  

randomEllipticAboSurface0=method(Options=>{Verbose=>false,Count=>false,
	PrintConstructionData=>false})
  ---finds elliptic Abo surfaces from (4x5) matrices over the plane, s.t. the Bordiga matrix has three rank one points
 randomEllipticAboSurface0( Ring, Ring):= opt -> (P4,P2) -> (
 kk := coefficientRing P4;
    e:= symbol e;
     P2xP4:= P2**P4;
    E := kk[e_0..e_4,SkewCommutative=>true];
    m1x3 := matrix{{e_0,e_1,e_2}};
       a:=symbol a;
    b:=symbol b;
    bs := flatten apply(3,i->flatten apply(3,j->apply(10,k->b_(i,j,k))));
    as := flatten apply(1,i->flatten apply(4,j->apply(10,k->a_(i,j,k))));
    B := kk[bs,as];
    ExB := E**B;
    E2 := sub(basis(2,E),ExB);
    a1x4 := matrix apply(1,i->apply(4,j->sum(10,k->(sub(a_(i,j,k),ExB)*E2_(0,k)))));
    b3x3 := matrix apply(3,i->apply(3,j->sum(10,k->(sub(b_(i,j,k),ExB)*E2_(0,k)))));
    E3 := sub(basis(3,E),ExB);
    m4x3 := transpose((transpose sub(m1x3,ExB)) | b3x3);
    count:=1;count1:=1;count2:=1;
    isSurface := false;
    ek1:= null;k31:=null;ek2:= null;k32:=null;ek3:= null;k33:=null;ek4:= null;k34:=null;
    m3x4:=null;m4x4:=null;c :=null;Is:=null;sol:=null;randsol:=null;a1x4s:=null;
    m4x4s:=null;bb:=null;tau:=null;beta0:=null;alpha':=null;alpha0:=null;
    beta:=null;alpha:=null;F:=null;delta:=null;I:=null;randSols:=null;rIs:=null;
    m4x5:=null;Irs:=null;
    while ( --get smooth surface
   -- count1=1;	
    while ( -- get surface of degree 12
	 -- count=1;
          while ( -- syz bb as desired
	      while (
	     m4x5=random(P2^4,P2^1)*( transpose matrix { {P2_0}})|random(P2^4,P2^1)*( transpose matrix { {P2_1}})|random(P2^4,P2^3)*(transpose vars P2)|random(P2^4,P2^1)*( transpose matrix { {P2_2}})|random(P2^4,P2^3)*(transpose vars P2);
           m3x4=sub(transpose (sub(diff(sub(vars P2,P2xP4),transpose (sub(vars P4,P2xP4)*sub(transpose m4x5,P2xP4))),P4)), vars E);
--mE3x4=sub(m3x4, vars E);
	      --m3x4 = k31|k32|k33|k34;
	      m4x4 = (transpose a1x4) | (transpose sub(m3x4,ExB));
	      c = m4x4*m4x3;
	      Is = trim ideal sub(contract(E3,flatten c),B);
	      rIs=rank source gens Is;
	      not (rIs==109)) do count=count+1;
	  --    if opt.PrintConstructionData and opt.Verbose then (
	--	  <<"betti Is= " << betti Is <<endl);
	      sol = vars B%Is;
	      randSols = sub(sol,random(kk^1,kk^130));
	      a1x4s = sub(a1x4,vars E|randSols);
	      m4x4s = (transpose a1x4s) | (transpose m3x4);
	      bb = map(E^4,,m4x4s);
	      tau = syz bb;
	     -- if opt.PrintConstructionData and opt.Verbose then (
	--	  <<"betti syz bb = " << betti tau <<endl);
	      not ((tally degrees source tau)_{3} == 3 and 
		  (tally degrees source tau)_{4} == 5 )) do count1=count1+1;
--	  if opt.Verbose then << "count= " <<count << endl;
          beta0 = bb;
	  alpha' = submatrix(tau,,{0,1,2});
	  alpha0 = alpha' | (sub(tau,E)*random(source sub(tau,E),E^{1:-4}));
	  beta = beilinson(beta0,P4);
	  alpha = beilinson(alpha0,P4);
	  F = prune homology(beta,alpha);
	  delta = syz transpose presentation F;
	  I = ideal (delta);
          not (degree I == 12 and codim I == 2) )
      do (count2=count2+1);
       if opt.Verbose then << "count= " <<count << endl;
     -- if opt.Count then << "count1= " << count1 <<endl;
     if opt.PrintConstructionData then (
	      <<Irs <<endl;
--	      <<"betti syz bb = " << betti tau <<endl);
      singX:= singularLocus I; 
    --  if opt.PrintConstructionData then (
--	  <<"codim singX = " << codim singX <<endl);
      not codim singX == 5)) do ( );
      if opt.Count then << "count2= " << count2 <<endl;      
      (I, m3x4, rIs))





 randomEllipticAboSurface3=method(Options=>{Verbose=>false,Count=>false,
	PrintConstructionData=>false})
  ---finds elliptic Abo surfaces from (4x5) matrices over the plane, s.t. the Bordiga matrix has three rank one points
 randomEllipticAboSurface3( Ring, Ring):= opt -> (P4,P3) -> (
 kk := coefficientRing P4;
    e:= symbol e;
     P3xP4 := P3**P4;
    E := kk[e_0..e_4,SkewCommutative=>true];
    m1x3 := matrix{{e_0,e_1,e_2}};
       a:=symbol a;
    b:=symbol b;
    bs := flatten apply(3,i->flatten apply(3,j->apply(10,k->b_(i,j,k))));
    as := flatten apply(1,i->flatten apply(4,j->apply(10,k->a_(i,j,k))));
    B := kk[bs,as];
    ExB := E**B;
    E2 := sub(basis(2,E),ExB);
    a1x4 := matrix apply(1,i->apply(4,j->sum(10,k->(sub(a_(i,j,k),ExB)*E2_(0,k)))));
    b3x3 := matrix apply(3,i->apply(3,j->sum(10,k->(sub(b_(i,j,k),ExB)*E2_(0,k)))));
    E3 := sub(basis(3,E),ExB);
    m4x3 := transpose((transpose sub(m1x3,ExB)) | b3x3);
    count:=1;count1:=1;count2:=1;
    isSurface := false;
    ek1:= null;k31:=null;ek2:= null;k32:=null;ek3:= null;k33:=null;ek4:= null;k34:=null;
    m3x4:=null;m4x4:=null;c :=null;Is:=null;sol:=null;randsol:=null;a1x4s:=null;
    m4x4s:=null;bb:=null;tau:=null;beta0:=null;alpha':=null;alpha0:=null;
    beta:=null;alpha:=null;F:=null;delta:=null;I:=null;randSols:=null;rIs:=null;
    while ( --get smooth surface
   -- count1=1;	
    while ( -- get surface of degree 12
	 -- count=1;
          while ( -- syz bb as desired
	      while (
m3x5:=matrix {{P3_0},{0},{0}}|matrix { {0},{P3_1},{0}}|random(P3^3,P3^4)*(transpose vars P3)|matrix {{0},{0},{P3_2}}|transpose(transpose(random(P3^2,P3^3)*matrix {{P3_0},{P3_1},{P3_3}})|random(P3^1,P3^4)*(transpose vars P3));
m3x4=sub(transpose (sub(diff(sub(vars P3,P3xP4),transpose (sub(vars P4,P3xP4)*sub(transpose m3x5,P3xP4))),P4)), vars E);
--mE3x4=sub(m3x4, vars E);
	      --m3x4 = k31|k32|k33|k34;
	      m4x4 = (transpose a1x4) | ( sub(m3x4,ExB));
	      c = m4x4*m4x3;
	      Is = trim ideal sub(contract(E3,flatten c),B);
	      rIs=rank source gens Is;
	  --   if opt.PrintConstructionData and opt.Verbose then (
       	 -- << rIs <<endl);
	 not (rIs==109)) do (count=count+1);
	      sol = vars B%Is;
	      randSols = sub(sol,random(kk^1,kk^130));
	      a1x4s = sub(a1x4,vars E|randSols);
	      m4x4s = (transpose a1x4s) | ( m3x4);
	      bb = map(E^4,,m4x4s);
	      tau = syz bb;
	     -- if opt.PrintConstructionData and opt.Verbose then (
	--	  <<"betti syz bb = " << betti tau <<endl);
	      not ((tally degrees source tau)_{3} == 3 and 
		  (tally degrees source tau)_{4} == 5 )) do (count2=count2+1);
--	  if opt.Verbose then << "count= " <<count << endl;
          beta0 = bb;
	  alpha' = submatrix(tau,,{0,1,2});
	  alpha0 = alpha' | (sub(tau,E)*random(source sub(tau,E),E^{1:-4}));
	  beta = beilinson(beta0,P4);
	  alpha = beilinson(alpha0,P4);
	  F = prune homology(beta,alpha);
	  delta = syz transpose presentation F;
	  I = ideal (delta);
          not (degree I == 12 and codim I == 2) )
      do (count1=count1+1);
       if opt.Verbose then << "count= " <<count << endl;
      if opt.Count then << "count1= " << count1 <<endl;
     -- if opt.PrintConstructionData then (
--	      <<"betti Is= " << betti Is <<endl;
--	      <<"betti syz bb = " << betti tau <<endl);
      singX:= singularLocus I; 
    --  if opt.PrintConstructionData then (
--	  <<"codim singX = " << codim singX <<endl);
      not codim singX == 5) do ();
      if opt.Count then << "count2= " << count2 <<endl;      
      (I, m3x4, rIs))






randomEllipticAboSurface2=method(Options=>{Verbose=>false,Count=>false,PrintConstructionData=>false})
  ---finds elliptic Abo surfaces from (3x5) matrices over P3, s.t. the Bordiga matrix has two rank one points
  randomEllipticAboSurface2( Ring, Ring):= opt -> (P4,P3) -> (
 kk := coefficientRing P4;
    e:= symbol e;
     P3xP4 := P3**P4;
    E := kk[e_0..e_4,SkewCommutative=>true];
    m1x3 := matrix{{e_0,e_1,e_2}};
       a:=symbol a;
    b:=symbol b;
    bs := flatten apply(3,i->flatten apply(3,j->apply(10,k->b_(i,j,k))));
    as := flatten apply(1,i->flatten apply(4,j->apply(10,k->a_(i,j,k))));
    B := kk[bs,as];
    ExB := E**B;
    E2 := sub(basis(2,E),ExB);
    a1x4 := matrix apply(1,i->apply(4,j->sum(10,k->(sub(a_(i,j,k),ExB)*E2_(0,k)))));
    b3x3 := matrix apply(3,i->apply(3,j->sum(10,k->(sub(b_(i,j,k),ExB)*E2_(0,k)))));
    E3 := sub(basis(3,E),ExB);
    m4x3 := transpose((transpose sub(m1x3,ExB)) | b3x3);
    count:=1;count1:=1;count2:=1;
    isSurface := false;
    ek1:= null;k31:=null;ek2:= null;k32:=null;ek3:= null;k33:=null;ek4:= null;k34:=null;
    m3x4:=null;m4x4:=null;c :=null;Is:=null;sol:=null;randsol:=null;a1x4s:=null;
    m4x4s:=null;bb:=null;tau:=null;beta0:=null;alpha':=null;alpha0:=null;
    beta:=null;alpha:=null;F:=null;delta:=null;I:=null;randSols:=null;m3x5:=null;
    rIs:=null;
    while ( --get smooth surface
   -- count1=1;	
    while ( -- get surface of degree 12
	 -- count=1;
          while ( -- syz bb as desired
	      while (
m3x5= transpose(matrix {{0}}|transpose(random(P3^2,P3^1)*matrix {{P3_1}}))|transpose(transpose(random(P3^2,P3^3)*matrix {{P3_1},{P3_2},{P3_3}})|random(P3^1,P3^4)*(transpose vars P3))|random(P3^3,P3^4)*(transpose vars P3)|matrix {{0},{0},{P3_0}}|random(P3^3,P3^3)*matrix {{P3_1},{P3_2},{P3_3}};
m3x4=sub(transpose (sub(diff(sub(vars P3,P3xP4),transpose (sub(vars P4,P3xP4)*sub(transpose m3x5,P3xP4))),P4)), vars E);
	      m4x4 = (transpose a1x4) | ( sub(m3x4,ExB));
	      c = m4x4*m4x3;
	      Is = trim ideal sub(contract(E3,flatten c),B);
	      rIs=rank source gens Is;
	  --   if opt.PrintConstructionData and opt.Verbose then (
       	 -- << rIs <<endl);
	 not (rIs==109)) do (count=count+1);
	      sol = vars B%Is;
	      randSols = sub(sol,random(kk^1,kk^130));
	      a1x4s = sub(a1x4,vars E|randSols);
	      m4x4s = (transpose a1x4s) | ( m3x4);
	      bb = map(E^4,,m4x4s);
	      tau = syz bb;
	     -- if opt.PrintConstructionData and opt.Verbose then (
	--	  <<"betti syz bb = " << betti tau <<endl);
	      not ((tally degrees source tau)_{3} == 3 and 
		  (tally degrees source tau)_{4} == 5 )) do (count2=count2+1);
--	  if opt.Verbose then << "count= " <<count << endl;
          beta0 = bb;
	  alpha' = submatrix(tau,,{0,1,2});
	  alpha0 = alpha' | (sub(tau,E)*random(source sub(tau,E),E^{1:-4}));
	  beta = beilinson(beta0,P4);
	  alpha = beilinson(alpha0,P4);
	  F = prune homology(beta,alpha);
	  delta = syz transpose presentation F;
	  I = ideal (delta);
          not (degree I == 12 and codim I == 2) )
      do (count1=count1+1);
       if opt.Verbose then << "count= " <<count << endl;
      if opt.Count then << "count1= " << count1 <<endl;
     -- if opt.PrintConstructionData then (
--	      <<"betti Is= " << betti Is <<endl;
--	      <<"betti syz bb = " << betti tau <<endl);
      singX:= singularLocus I; 
    --  if opt.PrintConstructionData then (
--	  <<"codim singX = " << codim singX <<endl);
      not codim singX == 5) do ();
      if opt.Count then << "count2= " << count2 <<endl;      
      (I, m3x4, rIs))


  randomEllipticAboSurface1=method(Options=>{Verbose=>false,Count=>false,PrintConstructionData=>false})
  ---finds elliptic Abo surfaces from (3x5) matrices over P3, s.t. the Bordiga matrix has one rank one point
  randomEllipticAboSurface1( Ring, Ring):= opt -> (P4,P3) -> (
 kk := coefficientRing P4;
    e:= symbol e;
     P3xP4 := P3**P4;
    E := kk[e_0..e_4,SkewCommutative=>true];
    m1x3 := matrix{{e_0,e_1,e_2}};
       a:=symbol a;
    b:=symbol b;
    bs := flatten apply(3,i->flatten apply(3,j->apply(10,k->b_(i,j,k))));
    as := flatten apply(1,i->flatten apply(4,j->apply(10,k->a_(i,j,k))));
    B := kk[bs,as];
    ExB := E**B;
    E2 := sub(basis(2,E),ExB);
    a1x4 := matrix apply(1,i->apply(4,j->sum(10,k->(sub(a_(i,j,k),ExB)*E2_(0,k)))));
    b3x3 := matrix apply(3,i->apply(3,j->sum(10,k->(sub(b_(i,j,k),ExB)*E2_(0,k)))));
    E3 := sub(basis(3,E),ExB);
    m4x3 := transpose((transpose sub(m1x3,ExB)) | b3x3);
    count:=1;count1:=1;count2:=1;
    isSurface := false;
    ek1:= null;k31:=null;ek2:= null;k32:=null;ek3:= null;k33:=null;ek4:= null;k34:=null;
    m3x4:=null;m4x4:=null;c :=null;Is:=null;sol:=null;randsol:=null;a1x4s:=null;
    m4x4s:=null;bb:=null;tau:=null;beta0:=null;alpha':=null;alpha0:=null;
    beta:=null;alpha:=null;F:=null;delta:=null;I:=null;randSols:=null;m3x5:=null;
    rIs:=null;
    while ( --get smooth surface
   -- count1=1;	
    while ( -- get surface of degree 12
	 -- count=1;
          while ( -- syz bb as desired
	      while (
m3x5= transpose(transpose(random(P3^2,P3^3)*matrix {{P3_1},{P3_2},{P3_3}})|random(P3^1,P3^4)*(transpose vars P3))|transpose(transpose(random(P3^2,P3^3)*matrix {{P3_1},{P3_2},{P3_3}})|random(P3^1,P3^4)*(transpose vars P3))|random(P3^3,P3^4)*(transpose vars P3)|matrix {{0},{0},{P3_0}}|random(P3^3,P3^3)*matrix {{P3_1},{P3_2},{P3_3}};
m3x4=sub(transpose (sub(diff(sub(vars P3,P3xP4),transpose (sub(vars P4,P3xP4)*sub(transpose m3x5,P3xP4))),P4)), vars E);
--mE3x4=sub(m3x4, vars E);
	      --m3x4 = k31|k32|k33|k34;
	      m4x4 = (transpose a1x4) | ( sub(m3x4,ExB));
	      c = m4x4*m4x3;
	      Is = trim ideal sub(contract(E3,flatten c),B);
	      rIs=rank source gens Is;
	  --   if opt.PrintConstructionData and opt.Verbose then (
       	 -- << rIs <<endl);
	 not (rIs==109)) do (count=count+1);
	      sol = vars B%Is;
	      randSols = sub(sol,random(kk^1,kk^130));
	      a1x4s = sub(a1x4,vars E|randSols);
	      m4x4s = (transpose a1x4s) | ( m3x4);
	      bb = map(E^4,,m4x4s);
	      tau = syz bb;
	     -- if opt.PrintConstructionData and opt.Verbose then (
	--	  <<"betti syz bb = " << betti tau <<endl);
	      not ((tally degrees source tau)_{3} == 3 and 
		  (tally degrees source tau)_{4} == 5 )) do (count2=count2+1);
--	  if opt.Verbose then << "count= " <<count << endl;
          beta0 = bb;
	  alpha' = submatrix(tau,,{0,1,2});
	  alpha0 = alpha' | (sub(tau,E)*random(source sub(tau,E),E^{1:-4}));
	  beta = beilinson(beta0,P4);
	  alpha = beilinson(alpha0,P4);
	  F = prune homology(beta,alpha);
	  delta = syz transpose presentation F;
	  I = ideal (delta);
          not (degree I == 12 and codim I == 2) )
      do (count1=count1+1);
       if opt.Verbose then << "count= " <<count << endl;
      if opt.Count then << "count1= " << count1 <<endl;
     -- if opt.PrintConstructionData then (
--	      <<"betti Is= " << betti Is <<endl;
--	      <<"betti syz bb = " << betti tau <<endl);
      singX:= singularLocus I; 
    --  if opt.PrintConstructionData then (
--	  <<"codim singX = " << codim singX <<endl);
      not codim singX == 5) do ();
      if opt.Count then << "count2= " << count2 <<endl;      
      (I, m3x4, rIs))
  

partitionOfCanonicalDivisorOfAboSurface=method(Options=>{Verbose=>false,Equations=>false})
partitionOfCanonicalDivisorOfAboSurface(Ideal) := opt -> X -> (
    P4:= ring X;
    p:=char P4;
    betti (omega:=Ext^1(module X,P4^{-5}));
    betti(m10x22:= presentation trim omega);
    betti(m9x22:=m10x22^{1..9});
    betti(K:=ann coker m9x22);
    if opt.Equations then return K;
    assert((dim K, degree K)==(2,12));
    --minimalBetti K
    cK:=primaryDecomposition K;
    r:=lcm apply(cK,c->degree c);
    -- we pass to a finite field extension where all component become distinct
    -- i.e. we compute the absolutely irreducible components.
    kk2:=GF(p,r);
    P42:=kk2[gens P4];
    cK':=flatten apply(cK,c->decompose sub(c,P42));   
    if sum(cK',c->degree c)=!=12 then (
	cK'':=flatten apply(cK,c->primaryDecomposition sub(c,P42));
	cK''=sort(cK'',c->degree c);
	if opt.Verbose then (
	<< minimalBetti X <<endl;
        << apply(cK'',c->(degree c,degree radical c)) <<endl;
        << matrix apply(cK'',c->apply(cK'',d->dim (c+d))) <<endl);
    -- return (apply(cK'',c->(degree c,degree radical c)),matrix apply(cK'',c->apply(cK'',d->dim (c+d))))
    );
    sort apply(cK',c->degree c))


analyzeAboSurface=method(Options=>{PrintConstructionData=>false,Verbose=>false})
analyzeAboSurface(Ring) := opt -> P4 -> (
   X:=randomAboSurface(P4,PrintConstructionData=>opt.PrintConstructionData);
   K:=partitionOfCanonicalDivisorOfAboSurface (X,opt);
   residual:=residualInQuintics X;
   if opt.Verbose then (
       << "reduced components of K have degree= " << K <<endl;
       << "residualInQuintics = " << residual <<endl;
       );
   (K,residual))

analyzeAboSurface(Ideal) := opt -> X -> (
   K:=partitionOfCanonicalDivisorOfAboSurface (X,Verbose=>true);
   residual:=residualInQuintics X;
   if opt.Verbose then (
       << "reduced components of K have degree= " << K <<endl;
       << "residualInQuintics = " << residual <<endl;
       );
   (K,residual))

analyzeAboSurface(ZZ,Ring):= opt -> (n,P4) -> (
    tally apply(n,c->(<<c<<endl;
	    elapsedTime analyzeAboSurface(P4,PrintConstructionData=>opt.PrintConstructionData)))
)
    


numericalTypeOfResidualInQuintics=method()

numericalTypeOfResidualInQuintics(Ideal,Ideal) := (R,X) -> (
    cR:= primaryDecomposition R;
    m:=null;
    numType:=flatten apply(cR,c->if dim c == 2 then (
		m=(1-genus c);
		if degree (c+X)== m*6 then apply(m,j->((2,1),(1,6))) else
		{((dim c, degree c),(dim(c+X),degree(c+X)))})
		else {((dim c, degree c),(dim(c+X),degree(c+X)))}
		)
	    )
///
kk=ZZ/7
P4=kk[x_0..x_4]
E=kk[e_0..e_4,SkewCommutative=>true]
setRandomSeed("same start");
elapsedTime (X,m3x4)=randomAboSurface(P4,E);
setRandomSeed("same start");
saturate minors(2,sub(m3x4,vars P4))
elapsedTime (Xs,m3x4s)=randomSpecialAboSurface(P4,E);
pt=saturate minors(2,sub(m3x4s,vars P4))
sub(m3x4s,vars P4)%pt

///

randomSpecialAboSurface=method(Options=>{Verbose=>false,Count=>false,
	PrintConstructionData=>false})

randomSpecialAboSurface(Ring,Ring) := opt -> (P4,E) -> (
    assert(char P4==char E);
    kk:=coefficientRing E;
    y:= symbol y;z:=symbol z;
    P2:=kk[y_0..y_2];
    P3:=kk[z_0..z_3];    
    r:=null;
    while (r=random(kk);member(r, {1_kk,0_kk})) do ();
    m1x3 := matrix{{E_0,E_1,E_2}};
    p1 := matrix{{E_1,E_2,E_3}};
    p2 := matrix{{E_1,E_2,E_4}};
    p3 := matrix{{E_1,E_2,E_4-random(kk)*E_3}};
    p4 := matrix{{E_1,E_2,E_4-E_3}};
    a:=symbol a;
    b:=symbol b;
    bs := flatten apply(3,i->flatten apply(3,j->apply(10,k->b_(i,j,k))));
    as := flatten apply(1,i->flatten apply(4,j->apply(10,k->a_(i,j,k))));
    B := kk[bs,as];
    ExB := E**B;
    E2 := sub(basis(2,E),ExB);
    a1x4 := matrix apply(1,i->apply(4,j->sum(10,k->(sub(a_(i,j,k),ExB)*E2_(0,k)))));
    b3x3 := matrix apply(3,i->apply(3,j->sum(10,k->(sub(b_(i,j,k),ExB)*E2_(0,k)))));
    E3 := sub(basis(3,E),ExB);
    m4x3 := transpose((transpose sub(m1x3,ExB)) | b3x3);
    count:=1;count1:=1;count2:=1;
    isSurface := false;
    ek1:= null;k31:=null;ek2:= null;k32:=null;ek3:= null;k33:=null;ek4:= null;k34:=null;
    m3x4:=null;m4x4:=null;c :=null;Is:=null;sol:=null;randsol:=null;a1x4s:=null;
    m4x4s:=null;bb:=null;tau:=null;beta0:=null;alpha':=null;alpha0:=null;
    beta:=null;alpha:=null;F:=null;delta:=null;I:=null;randSols:=null;n34:=null;
    rIs:=null; mn3x4:=null;
    while ( --get smooth surface
    count1=1;	
    while ( -- get surface of degree 12
	  count=1;
          while ( -- syz bb as desired
	      ek1 = random(E^2,E^3)*transpose p1;
	      k31 = random(E^3,E^2)*ek1;
	      ek2 = random(E^2,E^3)*transpose p2;
	      k32 = random(E^3,E^2)*ek2;
	      ek3 = random(E^2,E^3)*transpose p3;
	      k33 = random(E^3,E^2)*ek3;
	      ek4 = random(E^2,E^3)*transpose p4;
	      k34 = random(E^3,E^2)*ek4;
	      mn3x4 = k31|k32|k33|k34;
	      n34=transpose(matrix{{E_0}}*random(E^1,E^3))*random(E^1,E^4);
	      m3x4=mn3x4+n34;
	      if opt.PrintConstructionData then << (adjointMatrices(m3x4,P2,P3,P4)) <<endl;
	      m4x4 = (transpose a1x4) | (transpose sub(m3x4,ExB));
	      c = m4x4*m4x3;
	      Is = trim ideal sub(contract(E3,flatten c),B);
	      rIs=rank source gens Is;
	      if opt.PrintConstructionData and opt.Verbose then (
		  <<"betti Is= " << betti Is <<endl);
	      sol = vars B%Is;
	      randSols = sub(sol,random(kk^1,kk^130));
	      a1x4s = sub(a1x4,vars E|randSols);
	      m4x4s = (transpose a1x4s) | (transpose m3x4);
	      bb = map(E^4,,m4x4s);
	      tau = syz bb;
	      if opt.PrintConstructionData and opt.Verbose then (
		  <<"betti syz bb = " << betti tau <<endl);
	      not ((tally degrees source tau)_{3} == 3 and 
		  (tally degrees source tau)_{4} == 5 )) do count=count+1;
	  if opt.Verbose then << "count= " <<count << endl;
          beta0 = bb;
	  alpha' = submatrix(tau,,{0,1,2});
	  alpha0 = alpha' | (sub(tau,E)*random(source sub(tau,E),E^{1:-4}));
	  beta = beilinson(beta0,P4);
	  alpha = beilinson(alpha0,P4);
	  F = prune homology(beta,alpha);
	  delta = syz transpose presentation F;
	  I = ideal (delta);
          not (degree I == 12 and codim I == 2) )
      do (count1=count1+1);
      if opt.Count then << "count1= " << count1 <<endl;
      if opt.PrintConstructionData then (
	      <<"betti Is= " << betti Is <<endl);
	     -- <<"betti syz bb = " << betti tau <<endl);
      singX:= singularLocus I; 
      if opt.PrintConstructionData then (
	  <<"codim singX = " << codim singX <<endl);
      not codim singX == 5) do (count2=count2+1);
      if opt.Count then << "count2= " << count2 <<endl;      
      (I,m3x4))



collectAboSurfaces=method(Options=>{Verbose=>true,Special=>false})	
collectAboSurfaces(List,Ring,Ring,ZZ) := opt -> (mdKRs,P4,E,N) -> (
    count:= #mdKRs;count1:=0;
    ms:=apply(mdKRs,m->m_0);KRs:=apply(mdKRs,m->m_2);mdKRs':=mdKRs;
    X:=null; m3x4:= null;K:=null; R:= null; R1:=null; cR1:=null; T0:=null;Xs':=null;KRs':=KRs;
    d:=null;
    while (count<N) do (
	elapsedTime if opt.Special then (X,m3x4)=randomSpecialAboSurface(P4,E,Verbose=>false) else (
	(X,m3x4)=randomAboSurface(P4,E,Verbose=>false);
	);
	d=testMatrix2(map(E^3,,m3x4),P4);
	K = partitionOfCanonicalDivisorOfAboSurface(X,Verbose=>true);
	if opt.Verbose then << "K = " << K <<endl;
	R1 = residualInQuintics X; count1=count1+1;
	R = tally numericalTypeOfResidualInQuintics(R1,X);
	if opt.Verbose then << "count1= "<<count1 <<endl;
	if #select(KRs,KR-> (K,R)==KR)<15 then (
	    count=count+1;
	    if opt.Verbose then <<"count=" <<count <<", (K,R)= " << (K,R) <<", dim Hom = " << d<<flush<< endl; 
	    KRs=append(KRs,(K,R));
	    mdKRs'=append(mdKRs',(m3x4,d,(K,R))););
	);
    << "count1= "<<count1 <<endl;
    mdKRs')


-*
collectSpecialAboSurfaces=method(Options=>{Verbose=>true})	
collectSpecialAboSurfaces(List,Ring,Ring,ZZ) := opt -> (mdKRs,P4,E,N) -> (
    count:= #mdKRs;count1:=0;
    ms:=apply(mdKRs,m->m_0);KRs:=apply(mKRs,m->m_2);mKRs':=mKRs;
    X:=null; m3x4:= null;K:=null; R:= null; R1:=null; cR1:=null; T0:=null;Xs':=null;KRs':=KRs;
    n:=0;d:=null;
    while (count<N) do (
	(X,m3x4,n)=randomSpecialAboSurface(P4,E,Verbose=>false);
	d=testMatrix2(m3x4,P4);
	K = partitionOfCanonicalDivisorOfAboSurface(X,Verbose=>true);
	if opt.Verbose then << "K = " << K <<endl;
	R1 = residualInQuintics X; count1=count1+1;
	R = tally numericalTypeOfResidualInQuintics(R1,X);
	if opt.Verbose then << "count1= "<<count1 <<endl;
	if #select(KRs,KR-> (K,R)==KR)<20 then (
	    count=count+1;
	    if opt.Verbose then <<"count=" <<count <<" (K,R)= " << (K,R) << endl;
	    KRs=append(KRs,(K,R));
	    mdKRs'=append(mKRs',(m3x4,d,(K,R))););
	);
    << "count1= "<<count1 <<endl;
    mdKRs')
*-

specificEllipticAboSurfaceD12S13=method(Options=>{Verbose=>false})

specificEllipticAboSurfaceD12S13(Ring,Ring,Number) := o -> (P4,E,k) -> (
    p:=char P4;
    if not member(p,{31}) then return (<<"no example stored for p = "<<p<<flush<<endl;
	return ideal 0_P4);
    if p==31 then (
	mdKRs := {(matrix {{6*E_0-4*E_2-11*E_4, 13*E_0-14*E_2+15*E_4, 15*E_0+11*E_2+8*E_4,
			-15*E_0+E_2-15*E_4}, {-12*E_1+5*E_2-3*E_4, -15*E_1+11*E_2-6*E_4,
      -14*E_1-14*E_2-13*E_4, -7*E_1-9*E_2-7*E_4}, {12*E_2-14*E_3+10*E_4,
      11*E_2-10*E_3-3*E_4, 10*E_2+8*E_3-12*E_4, 8*E_2-8*E_3+3*E_4}},6,
    ({1, 1, 1, 1, 2, 2, 4},new Tally from {(1,1,(0,6)) => 3, (2,2,(1,8,9)) => 1}))};
    if o.Verbose then ( << "#mdKRs = " << #mdKRs <<endl);
     if not k <#mdKRs then (<<"only "|#mdKRs|" examples stored"<<flush<<endl;return ideal 1_(P4));
      mdKR:=mdKRs_k;
      if o.Verbose then (
      << "(K,R) = " << mdKR_2 <<", dim Hom = " <<mdKR_1 <<flush<<endl;);
      m3x4:= mdKR_0;
      X:=aboSurfaceFromMatrix(m3x4,P4);
      return X)
  )

/// -* Test elliptic Abo surface *-
kk=ZZ/31;
P4=kk[x_0..x_4]
E=kk[e_0..e_4,SkewCommutative=>true]
elapsedTime X=specificEllipticAboSurfaceD12S13(P4,E,0,Verbose=>true);
K=canonicalDivisor X;
cK=primaryDecomposition K;
toString {1,1,1,1,2,2,4}
tally apply(cK,c->(dim c, degree c, degree radical c, genus c,
	selfIntersectionNumber(X,c)))

R=residualInQuintics X;
cR=primaryDecomposition R;
toString tally apply(cR,c->(dim c-1, degree c,(dim(c+X)-1,degree(c+X))))
///


specificAboSurface=method(Options=>{Verbose=>false})

specificAboSurface(Ring,Ring,Number) := o -> (P4,E,k) -> (
    p:=char P4;
    if not member(p,{7,11,19}) then return (<<"no example stored for p = "<<p<<flush<<endl;
	return ideal 0_P4);
    if p == 19 then (
    mdKRs:={(matrix {{0, -E_0+4*E_1+7*E_2-4*E_4, 8*E_0+7*E_1-9*E_2+9*E_3+4*E_4, -6*E_0+8*E_1+4*E_2+9*E_3-9*E_4},
      {-3*E_0+2*E_1-6*E_2, -8*E_0+2*E_1-5*E_2+E_4, 9*E_0-7*E_1-9*E_2-9*E_3-4*E_4, -9*E_0-3*E_1+7*E_2-2*E_3+2*E_4},
      {4*E_0-5*E_1-9*E_2+3*E_3, E_0-3*E_1+2*E_2+E_4, E_0+9*E_1+8*E_2-2*E_3-3*E_4,
      7*E_0+2*E_1-5*E_2+E_3-E_4}},1,({1, 2, 2, 2, 2, 3},new Tally from {((1,1),(0,6)) => 1, ((2,1),(1,6)) => 6})),
      (matrix {{-9*E_0+7*E_1-7*E_2-2*E_3, 3*E_0-2*E_1-9*E_4, 6*E_0-2*E_1-3*E_2-5*E_3-2*E_4,
      3*E_0+4*E_1-7*E_2-3*E_3+3*E_4}, {-8*E_0+5*E_1+6*E_2+8*E_3, 4*E_0-6*E_1+3*E_2-6*E_4,
      -6*E_0-2*E_1-3*E_2-4*E_3+6*E_4, 5*E_0-9*E_1+9*E_2+7*E_3-7*E_4}, {4*E_0-7*E_1+4*E_2-6*E_3,
      3*E_0-4*E_1-2*E_2+6*E_4, 5*E_0+3*E_1-5*E_2, -8*E_0-8*E_1+E_2-9*E_3+9*E_4}},1,({1, 1, 2, 2, 3, 3},new Tally
      from {((2,1),(1,6)) => 5})),(matrix {{2*E_0-6*E_1-5*E_2+E_3, -4*E_0+9*E_1+8*E_2+6*E_4, -6*E_0+6*E_1-5*E_2-2*E_3-2*E_4,
      4*E_0-8*E_1-7*E_2+2*E_3-2*E_4}, {7*E_0-8*E_1-5*E_2-4*E_3, 9*E_0-4*E_1+9*E_2-8*E_4,
      E_0-8*E_1+8*E_2-5*E_3-5*E_4, -4*E_0+2*E_1-6*E_2+5*E_3-5*E_4}, {E_0+5*E_1+3*E_2+E_3, E_0-8*E_1-6*E_2-9*E_4,
      5*E_0+6*E_1-8*E_2+E_3+E_4, -E_0-9*E_1+8*E_2+6*E_3-6*E_4}},1,({1, 1, 1, 3, 3, 3},new Tally from {((2,1),(1,6))
      => 4, ((2,4),(1,21)) => 1})),
    (matrix {{-2*E_0+9*E_1+E_4, -6*E_2, 6*E_0+2*E_1+7*E_2, 6*E_0-7*E_1}, {-6*E_0-3*E_1,
      E_2+E_3, -7*E_0+5*E_1+6*E_2+E_4, 7*E_0}, {4*E_1, 8*E_2, -9*E_1+6*E_2+E_3, -8*E_1+E_4}},2,
     ({1,1,2,2,2,4}, new Tally from {(2,1,(1,6)) => 1, (2,2,(1,11)) => 1, (2,4,(1,24)) => 1})),
  (matrix {{-5*E_0-5*E_1-5*E_2-8*E_3, -8*E_0-2*E_1+3*E_2-4*E_4,
      7*E_0+8*E_1-9*E_2-E_3+9*E_4, -9*E_0-2*E_1+7*E_3-7*E_4}, {-5*E_0-2*E_1+6*E_2-5*E_3, 3*E_0+7*E_1+E_2+9*E_4,
      6*E_0-2*E_1+2*E_3+E_4, 9*E_0+5*E_1+3*E_2-E_3+E_4}, {6*E_0+6*E_1+6*E_2+2*E_3, 8*E_0+E_1-6*E_2-E_4,
      -7*E_0-3*E_1-7*E_2, 3*E_0-2*E_1-9*E_2+5*E_3-5*E_4}},2,({1, 1, 1, 2, 3, 4},new Tally from {((2,1),(1,6)) => 4,
      ((2,2),(1,11)) => 1})),(matrix {{5*E_0+4*E_1+2*E_3, 3*E_0-5*E_1-9*E_2-5*E_4, 5*E_1+4*E_2,
      -4*E_0+2*E_1-4*E_2-9*E_3+9*E_4}, {2*E_0+2*E_1-7*E_2-3*E_3, 5*E_0-3*E_1+4*E_2+5*E_4, 0,
      6*E_0+E_1-6*E_2-8*E_3+8*E_4}, {3*E_0+6*E_1+7*E_2+7*E_3, -2*E_0+2*E_1+6*E_2, 4*E_1+7*E_2,
      9*E_0-7*E_1-6*E_2-5*E_3+5*E_4}},3,({1, 1, 1, 2, 2, 5},new Tally from {((2,1),(1,5)) => 1, ((2,1),(1,6)) => 5,
      ((3,1),(2,5)) => 1})), 
(matrix {{-E_0-4*E_2, 6*E_0+3*E_1+7*E_2-7*E_4, -9*E_0+9*E_2+E_3-E_4,
      -6*E_0+E_1+3*E_2+8*E_3-8*E_4}, {-7*E_0+2*E_1+9*E_2-2*E_3,
      -3*E_0+E_1+3*E_2+9*E_4, 9*E_0-8*E_1+E_2+5*E_3-5*E_4,
      7*E_0-3*E_1+6*E_2+7*E_3-7*E_4}, {2*E_0+4*E_1+6*E_2-4*E_3,
      4*E_0+2*E_2-4*E_4, -5*E_0-8*E_1-4*E_2-4*E_3+4*E_4,
      -9*E_0+9*E_1-5*E_2-3*E_3+3*E_4}},4,({1,1,1,1,4,4},new Tally from {(2,1,(1,6))=>3,(2,2,(1,11))=>2})),
(matrix {{-6*E_1-9*E_2, -9*E_0+4*E_1+3*E_2+2*E_4,
      -5*E_0-E_1-E_2-8*E_3+3*E_4, 4*E_0+8*E_1-9*E_2+7*E_3-7*E_4}, {-7*E_1-E_2,
      -3*E_0+6*E_1+8*E_4, -8*E_0-3*E_1+2*E_2-7*E_3+5*E_4,
      -5*E_0-9*E_1+E_2+E_3-E_4}, {-4*E_1-6*E_2, E_0-7*E_1+5*E_2+2*E_4,
      9*E_0-E_1+9*E_2+7*E_3-5*E_4, 8*E_0-8*E_1+8*E_3-8*E_4}},4,({1,1,1,1,2,6},
   new Tally from {(1,1,(0,5)) => 2, (1,1,(0,6)) => 4, (2,1,(1,5)) => 1})), 
(matrix {{6*E_0-E_1-8*E_2, -5*E_0+2*E_1+4*E_2, -7*E_1+2*E_2+3*E_3+3*E_4,
      4*E_0+9*E_1+2*E_2+6*E_3-6*E_4}, {5*E_0-6*E_1+8*E_2-5*E_3, -2*E_0-3*E_1-6*E_2, E_0-8*E_1-8*E_2+5*E_3+5*E_4,
      -3*E_0-8*E_1+7*E_2+5*E_3-5*E_4}, {9*E_0-8*E_1+4*E_2-2*E_3, E_0-8*E_1+3*E_2, -8*E_0+3*E_1-3*E_3-3*E_4,
      7*E_0+9*E_1+E_3-E_4}},5,({1, 1, 1, 1, 1, 7},new Tally from {((2,1),(1,5)) => 2, ((2,1),(1,6)) => 2,
      ((2,2),(1,11)) => 1, ((3,1),(2,5)) => 1}))

};
);
 
      if p==7 then (
       mdKRs= {(matrix {{3*E_0-E_3, 2*E_0+2*E_1-3*E_4, E_0+E_1-E_2-2*E_3+3*E_4, 2*E_0+3*E_2+3*E_3-3*E_4},
      {E_0-2*E_1-3*E_2+2*E_3, -2*E_0+E_1+2*E_2, -2*E_0+E_1-E_3-2*E_4, -2*E_0+2*E_1-3*E_2+3*E_3-3*E_4}, {-E_1+2*E_2,
      -2*E_0+3*E_1+E_2-2*E_4, -3*E_1+2*E_2-2*E_3+3*E_4, E_1+3*E_3-3*E_4}},2,({1, 1, 1, 1, 2, 3},new Tally from
      {((2,1),(1,5)) => 1, ((2,1),(1,6)) => 1, ((3,2),(2,8)) => 1})), (matrix {{3*E_1+2*E_2+E_3, 3*E_1-2*E_2, E_1,
      3*E_1+E_2}, {-3*E_0-E_1-3*E_2+2*E_3, 2*E_0+3*E_1+3*E_2+2*E_4, 2*E_1, -E_0-2*E_2+3*E_3-3*E_4},
      {E_0-E_1-E_2+3*E_3, -3*E_0-2*E_1+2*E_2-3*E_4, 0, -2*E_0+E_1-3*E_3+3*E_4}},4,({1, 1, 1, 1, 2, 6},new Tally
      from {((2,1),(1,5)) => 2, ((2,1),(1,6)) => 4, ((3,1),(2,5)) => 1})), (matrix {{E_0+E_1-E_2+E_3,
      -E_0+2*E_1+2*E_2-2*E_4, -E_0+3*E_1-2*E_2-2*E_4, -3*E_1+3*E_2+3*E_3-3*E_4}, {E_0-3*E_2-3*E_3,
      3*E_0+2*E_1-2*E_2, 3*E_1-2*E_2+3*E_4, E_0+2*E_1+3*E_2+2*E_3-2*E_4}, {E_0+E_1-E_2+E_3, -E_0-2*E_1+E_4,
      E_1-3*E_2+E_4, 2*E_0+2*E_1+E_2-E_3+E_4}},2,({1, 1, 1, 1, 1, 2},new Tally from {((2,1),(1,6)) => 4,
      ((2,2),(1,11)) => 1})), (matrix {{-2*E_0-3*E_1+2*E_2, E_0-E_1-3*E_2+2*E_4, -E_0+2*E_2,
      -2*E_1-2*E_2-3*E_3+3*E_4}, {-3*E_0+3*E_1-E_2+E_3, 2*E_0-3*E_1+2*E_2, 3*E_0+3*E_1+E_2-3*E_4,
      3*E_0+3*E_1-3*E_2+E_3-E_4}, {2*E_0+E_2+E_3, 3*E_0-E_1+3*E_2, -2*E_0+2*E_1-3*E_2-2*E_4,
      2*E_0-2*E_1+E_2-3*E_3+3*E_4}},1,({1, 1, 1, 2, 3, 3},new Tally from {((0,44),(0,42)) => 1, ((2,1),(1,6)) =>
      5})), (matrix {{E_0-2*E_1-E_2, 3*E_1+E_2+3*E_4, -2*E_1+2*E_2+2*E_3-3*E_4, 2*E_0-E_1-3*E_2},
      {2*E_0+3*E_1-2*E_2, -3*E_0-3*E_1-2*E_2, E_1-E_2-E_3-2*E_4, 3*E_0+2*E_1-3*E_2+E_3-E_4}, {2*E_0+3*E_1-2*E_2,
      -2*E_0-E_1-E_2+E_4, E_0-2*E_1+E_2-2*E_3+3*E_4, E_0+3*E_1-2*E_2+2*E_3-2*E_4}},5,({1, 1, 1, 1, 1, 7},new Tally
      from {((2,1),(1,5)) => 2, ((2,1),(1,6)) => 2, ((2,2),(1,11)) => 1, ((3,1),(2,5)) => 1})),
   (matrix {{-2*E_1+3*E_3, E_0+2*E_1+3*E_2+E_4, 3*E_0-E_1+E_2+E_3-3*E_4, 3*E_0-E_1-E_3+E_4}, {-3*E_0+2*E_1-2*E_2+3*E_3,
      -E_0+2*E_1-E_2+E_4, -E_0+3*E_1-2*E_2+3*E_3-2*E_4, -2*E_0+E_3-E_4}, {E_0-E_1+3*E_2+3*E_3, E_0-2*E_1+E_2-E_4,
      -3*E_1+E_2-2*E_3-E_4, -3*E_0+3*E_1}},2,({1, 1, 1, 2, 3, 4},new Tally from {((2,1),(1,6)) => 4, ((2,2),(1,11))
      => 1})), (matrix {{-E_1+2*E_2, -2*E_0-E_1-3*E_2-3*E_4, E_0-3*E_1+E_2+E_3-E_4, -3*E_0-E_1-E_2},
      {3*E_0-E_1+3*E_2+2*E_3, -2*E_0-E_1-3*E_2-3*E_4, -3*E_1+3*E_3-3*E_4, 2*E_0+2*E_1+E_2+E_3-E_4}, {E_0-E_1+3*E_3,
      2*E_0+2*E_1-2*E_4, -E_0+2*E_1-E_2, 2*E_1-3*E_2-2*E_3+2*E_4}},2,({1, 1, 1, 2, 2, 2},new Tally from
      {((2,1),(1,5)) => 1, ((2,1),(1,6)) => 3, ((2,2),(1,12)) => 1})), (matrix {{3*E_0+E_1-2*E_2-E_3,
      -E_0-E_1-E_2+3*E_4, 3*E_0-3*E_1-3*E_2-E_3+E_4, 2*E_1-3*E_3+3*E_4}, {3*E_0-2*E_1+E_2-2*E_3, 2*E_0+2*E_2+E_4,
      E_0+3*E_1-E_2+3*E_3-3*E_4, -2*E_0-3*E_2-2*E_3+2*E_4}, {2*E_0+3*E_1+E_2-3*E_3, 3*E_1,
      -2*E_0+E_1+2*E_2+E_3-E_4, -2*E_0-2*E_1-3*E_2+E_3-E_4}},2,({1, 1, 1, 2, 2, 3},new Tally from {((2,1),(1,5)) =>
      1, ((2,1),(1,6)) => 2, ((2,3),(1,18)) => 1})), (matrix {{2*E_0-3*E_1+E_2-3*E_3, E_0-3*E_1-E_2+2*E_4,
      2*E_1+E_2, 3*E_0+2*E_1-2*E_3+2*E_4}, {E_1+3*E_2+2*E_3, -E_1-3*E_2-2*E_4, 0, 2*E_1-2*E_3+2*E_4},
      {-E_0-2*E_1+2*E_3, 3*E_0-E_1-3*E_2-2*E_4, 2*E_1+E_2, 2*E_0+2*E_2+2*E_3-2*E_4}},2,({1, 1, 1, 2, 2, 4},new
      Tally from {((2,1),(1,6)) => 6, ((3,1),(2,5)) => 1})), (matrix {{3*E_0+E_1-E_2-3*E_3, -E_0+3*E_1+3*E_2-E_4,
      -3*E_0-2*E_1-2*E_2-3*E_3+3*E_4, -3*E_0-E_1-E_2-2*E_3+2*E_4}, {E_0, 2*E_0+E_1+E_2+2*E_4, -2*E_0+2*E_2-E_3+E_4,
      2*E_0+2*E_1+3*E_2+E_3-E_4}, {2*E_0+E_1-E_2-3*E_3, 2*E_0-E_1+2*E_2+3*E_4, 2*E_0-2*E_2+E_3-E_4,
      3*E_0-3*E_1+E_2+3*E_3-3*E_4}},2,({1, 1, 2, 2, 3, 3},new Tally from {((2,1),(1,5)) => 1, ((2,1),(1,6)) => 2,
      ((3,1),(2,4)) => 1})), (matrix {{-3*E_0, 3*E_1-3*E_2, -E_0-2*E_1+2*E_2+2*E_3+2*E_4,
      3*E_0-E_1+3*E_2+3*E_3-3*E_4}, {E_0-3*E_1+2*E_2-2*E_3, 2*E_1-2*E_2, -2*E_0+2*E_1-E_2+E_3+E_4, -E_0-E_1+E_2},
      {-3*E_0-E_1+E_3, 3*E_1-3*E_2, -E_0-E_1-3*E_2+3*E_3+3*E_4, 3*E_0+3*E_1+E_3-E_4}},3,({1, 1, 1, 2, 2, 5},new
      Tally from {((2,1),(1,6)) => 4, ((2,2),(1,11)) => 1, ((3,1),(2,5)) => 1})), (matrix {{-2*E_0-3*E_2,
      2*E_0+2*E_1+E_2-3*E_4, -3*E_0-2*E_1+2*E_2-E_3+2*E_4, E_0+2*E_2+E_3-E_4}, {3*E_2, E_0+E_1+3*E_2+2*E_4,
      E_0-2*E_1-3*E_2, -E_0-2*E_2-E_3+E_4}, {-E_0-3*E_2, -2*E_0-2*E_1+E_2+3*E_4, -2*E_0-2*E_1-E_2+E_3-2*E_4,
      E_0+E_1+E_2}},2,({1, 1, 2, 2, 2, 2},new Tally from {((1,1),(0,6)) => 1, ((2,1),(1,6)) => 5, ((2,2),(1,11)) =>
      1})), (matrix {{E_0-3*E_3, -2*E_1-2*E_4, -2*E_0+E_1-2*E_2+2*E_3-2*E_4, -E_0-3*E_1-2*E_3+2*E_4}, {3*E_0-2*E_3,
      E_0+E_1+2*E_2, -3*E_0+2*E_1+2*E_2+E_3-E_4, E_0+2*E_1+E_2}, {-2*E_0+E_1+E_2-E_3, -2*E_0-2*E_1+3*E_2,
      E_0-2*E_1-2*E_3+2*E_4, -E_0+3*E_1+E_2+3*E_3-3*E_4}},1,({1, 1, 2, 2, 2, 3},new Tally from {((1,1),(0,6)) => 1,
      ((2,1),(1,6)) => 6})), (matrix {{-E_0+2*E_1-3*E_2-2*E_3, -3*E_0-3*E_2+E_4, -3*E_0+2*E_1+2*E_3-E_4,
      -E_0+3*E_1+2*E_2+E_3-E_4}, {3*E_1-2*E_2+3*E_3, E_0+2*E_1-2*E_2+3*E_4, E_0+E_1+E_2+E_3+3*E_4,
      E_0-3*E_1-2*E_2-E_3+E_4}, {3*E_0+2*E_1-E_2, -3*E_0-E_1+2*E_2-3*E_4, 3*E_1-E_2+3*E_3+2*E_4,
      3*E_0-2*E_1-E_2-2*E_3+2*E_4}},1,({1, 2, 2, 2, 2, 2},new Tally from {((1,1),(0,6)) => 1, ((2,1),(1,6)) =>
      6})), (matrix {{-3*E_0-3*E_2+3*E_3, -E_0+3*E_1-2*E_2+3*E_4, E_0+E_1-E_2-2*E_4, -2*E_1+3*E_3-3*E_4},
      {-2*E_0+E_1-2*E_2+2*E_3, 3*E_0-3*E_1-E_2+2*E_4, -3*E_0-2*E_2-E_4, 3*E_3-3*E_4}, {-E_0-E_1-E_2+E_3,
      -E_1-3*E_4, E_0+2*E_1+2*E_2-2*E_4, -E_1+E_3-E_4}},2,({1, 1, 2, 2, 2, 4},new Tally from {((1,1),(0,6)) => 1,
      ((2,1),(1,6)) => 5, ((2,2),(1,11)) => 1})), (matrix {{3*E_0-2*E_1+2*E_2+E_3, -E_0+E_1-3*E_2-2*E_4,
      2*E_0+3*E_1+2*E_2, -E_0+2*E_1-2*E_2+E_3-E_4}, {E_0+E_1-3*E_2+2*E_3, E_0+E_1+2*E_2, -E_0+2*E_1-E_2,
      2*E_0+2*E_1+E_2-3*E_3+3*E_4}, {-E_0-2*E_1+E_2-3*E_3, E_1+3*E_2-E_4, 2*E_1+3*E_2-3*E_3-E_4,
      3*E_0+3*E_2+3*E_3-3*E_4}},1,({1, 2, 2, 2, 2, 3},new Tally from {((1,1),(0,6)) => 1, ((2,1),(1,6)) => 6})),
      (matrix {{-2*E_0+E_2-3*E_3, 3*E_0+E_1-3*E_2+E_4, 3*E_0-E_1-3*E_2, -E_0+E_1+E_2+2*E_3-2*E_4},
      {2*E_0-2*E_1-3*E_2+E_3, 2*E_0+3*E_1-2*E_2+3*E_4, -E_0+E_1-2*E_2+3*E_3-E_4, E_0+E_1-2*E_2-3*E_3+3*E_4},
      {-3*E_0+3*E_1+E_2+2*E_3, -E_0-E_1-E_2+E_4, -3*E_1+3*E_2-3*E_3+E_4, -E_0+2*E_1-3*E_2-2*E_3+2*E_4}},1,({1, 1,
      1, 3, 3, 3},new Tally from {((2,1),(1,3)) => 1, ((2,1),(1,6)) => 1, ((2,6),(1,36)) => 1}))});
      if p==11 then (
      mdKRs= {(matrix {{E_1-4*E_2+5*E_3, 5*E_0-2*E_1-3*E_2+E_4, 2*E_0+E_1-4*E_2+5*E_3+E_4, 5*E_0+4*E_1+E_2+4*E_3-4*E_4},
      {2*E_1+3*E_2-E_3, -E_0+4*E_1+4*E_2+2*E_4, 4*E_0-3*E_1+5*E_2+5*E_3+E_4, -E_0-5*E_1-E_2+E_3-E_4},
      {-3*E_1+3*E_2+4*E_3, E_0+5*E_1-5*E_2-5*E_4, -4*E_0+E_1-2*E_2+4*E_3+3*E_4, E_0+3*E_1-3*E_2+E_3-E_4}},2,({1, 2,
      2, 2, 2, 3},new Tally from {((1,1),(0,6)) => 1, ((2,1),(1,6)) => 2, ((2,2),(1,11)) => 1, ((3,1),(2,4)) =>
      1})), (matrix {{-5*E_1+E_2-E_3, -5*E_0+2*E_1-4*E_2-E_4, -2*E_0+E_1-3*E_2-2*E_3+2*E_4, -5*E_2-2*E_3+2*E_4},
      {-4*E_1-5*E_2+2*E_3, 2*E_0-4*E_1+4*E_2-3*E_4, 3*E_0+5*E_1-5*E_2+E_3-E_4, 2*E_1-E_2-4*E_3+4*E_4},
      {3*E_1+2*E_2+2*E_3, E_0+5*E_1-E_2-5*E_4, -4*E_0+2*E_1-2*E_2-4*E_3+4*E_4, -E_1+3*E_2+3*E_3-3*E_4}},2,({1, 1,
      2, 2, 3, 3},new Tally from {((2,1),(1,5)) => 1, ((2,1),(1,6)) => 2, ((3,1),(2,4)) => 1})),
  (matrix{{3*E_1-3*E_2, 2*E_0+2*E_1+2*E_2+3*E_4, -2*E_0-E_1-4*E_2+4*E_3-2*E_4, E_0+5*E_1+E_2+4*E_3-4*E_4},
      {-2*E_1+2*E_2, 4*E_0+4*E_1-2*E_4, -4*E_0-E_1-4*E_2+4*E_3-2*E_4, 2*E_0+5*E_1-3*E_2-3*E_3+3*E_4}, {E_1-E_2,
      3*E_0-E_1+5*E_2+5*E_4, -3*E_0-E_1-3*E_2+3*E_3+4*E_4, -4*E_0-2*E_1+2*E_2-4*E_3+4*E_4}},2,({1, 1, 2, 2, 2,
      4},new Tally from {((2,1),(1,6)) => 6, ((3,1),(2,5)) => 1})), (matrix {{-4*E_0-E_1-3*E_2-2*E_3, -2*E_2,
      3*E_0+4*E_1+E_2-2*E_3+E_4, -E_0+4*E_1+5*E_2-5*E_3+5*E_4}, {-3*E_0+4*E_1+E_2-3*E_3, -3*E_2,
      5*E_0+3*E_2-4*E_3+2*E_4, 2*E_0-4*E_2+E_3-E_4}, {-5*E_0-2*E_1-E_2-5*E_3, 2*E_2, E_0+4*E_1+3*E_3+4*E_4,
      -4*E_0-2*E_2-5*E_3+5*E_4}},2,({1, 1, 2, 2, 2, 2},new Tally from {((2,1),(1,6)) => 6, ((3,1),(2,5)) => 1})),
      (matrix {{3*E_0-3*E_1-2*E_2+2*E_3, -5*E_0-2*E_1+4*E_2+2*E_4, 5*E_0+5*E_1+2*E_2+3*E_3+2*E_4, -2*E_0},
      {-5*E_0+4*E_1+E_2-3*E_3, -5*E_0+E_1-2*E_2+E_4, -4*E_0+4*E_1+5*E_3-4*E_4, -E_0-4*E_2+3*E_3-3*E_4},
      {4*E_0+E_1-2*E_2+E_3, 2*E_0-2*E_1+4*E_2-5*E_4, 5*E_0-3*E_1-4*E_2, -2*E_0+2*E_2+4*E_3-4*E_4}},1,({1, 1, 1, 3,
      3, 3},new Tally from {((2,1),(1,6)) => 4, ((2,4),(1,21)) => 1})), (matrix {{-3*E_1-4*E_3, -2*E_0+2*E_1+2*E_4,
      5*E_0-5*E_1-2*E_2-E_3-4*E_4, -2*E_0+3*E_1-3*E_2+E_3-E_4}, {-4*E_2+4*E_3, 2*E_0+4*E_1+E_2,
      -5*E_0-E_1+3*E_2+3*E_3+E_4, 2*E_0+2*E_1-2*E_2-3*E_3+3*E_4}, {-4*E_1+2*E_2, -E_0-5*E_1+3*E_2+5*E_4,
      -3*E_0-2*E_1-2*E_2+3*E_3+E_4, -E_0+4*E_1-4*E_2+5*E_3-5*E_4}},2,({1, 1, 1, 2, 3, 3},new Tally from
      {((2,1),(1,5)) => 1, ((2,1),(1,6)) => 2, ((3,1),(2,4)) => 1})), (matrix {{4*E_0+4*E_1-3*E_2-4*E_3,
      -5*E_0+5*E_1+3*E_2-3*E_4, 3*E_0-5*E_1+2*E_2+3*E_3+3*E_4, 5*E_1+5*E_2}, {5*E_1+4*E_3, 2*E_1-3*E_4,
      3*E_1-4*E_2+4*E_3+4*E_4, -E_1-E_2}, {-5*E_0+4*E_2+3*E_3, -2*E_0+E_1+2*E_2-4*E_4, -E_0-E_1+2*E_2+2*E_3+2*E_4,
      2*E_1+2*E_2}},3,({1, 1, 1, 2, 2, 5},new Tally from {((2,1),(1,5)) => 1, ((2,1),(1,6)) => 5, ((3,1),(2,5)) =>
      1})), (matrix {{2*E_0+5*E_1-3*E_2, 5*E_1-E_2+E_4, 2*E_1+4*E_2, -3*E_0-3*E_1+2*E_2-3*E_3+3*E_4},
      {3*E_0+2*E_1+5*E_2+5*E_3, 2*E_1-4*E_2, -2*E_1-4*E_2, E_0-4*E_1-3*E_2-3*E_3+3*E_4}, {-5*E_0+2*E_1-3*E_2-5*E_3,
      E_1-3*E_2-5*E_4, E_1+2*E_2, 2*E_0+4*E_1-4*E_2+E_3-E_4}},3,({1, 1, 1, 2, 2, 4},new Tally from {((2,1),(1,5))
      => 1, ((2,1),(1,6)) => 5, ((3,1),(2,5)) => 1})), (matrix {{-3*E_1+E_2+5*E_3, -2*E_1+3*E_2-E_4,
      -4*E_1-4*E_2+5*E_3+2*E_4, -2*E_1}, {5*E_0+2*E_1-2*E_2-E_3, -5*E_0-2*E_1+4*E_2-5*E_4,
      -2*E_0-5*E_1+5*E_2+3*E_3-E_4, -3*E_1}, {-4*E_0+5*E_1-E_2-4*E_3, 4*E_0-5*E_1-2*E_2-3*E_4,
      -5*E_0+3*E_1-E_2-3*E_3+E_4, 2*E_1}},3,({1, 1, 1, 2, 2, 3},new Tally from {((2,1),(1,6)) => 4, ((2,2),(1,11))
      => 1, ((3,1),(2,5)) => 1})), (matrix {{-E_0+3*E_1+4*E_2+4*E_3, E_0+E_1+2*E_2-2*E_4,
      -5*E_0-4*E_1-5*E_2+2*E_3+4*E_4, 4*E_1}, {5*E_0-5*E_1-4*E_2-2*E_3, -5*E_0, 3*E_0-3*E_1-4*E_2-4*E_3+3*E_4,
      -4*E_1}, {-4*E_0-E_1+2*E_2-E_3, 4*E_0-5*E_1+E_2-E_4, 2*E_0-4*E_1-4*E_2+2*E_3+4*E_4, -3*E_1}},3,({1, 1, 1, 1,
      2, 5},new Tally from {((2,1),(1,5)) => 1, ((2,1),(1,6)) => 5, ((3,1),(2,5)) => 1})), (matrix {{2*E_0,
      -3*E_0-E_1+E_2-3*E_4, E_0-5*E_1+3*E_2+5*E_3-5*E_4, E_1-E_2}, {4*E_0-4*E_1-2*E_2-3*E_3,
      5*E_0+2*E_1-2*E_2+3*E_4, 2*E_0-4*E_1+5*E_2-2*E_3+2*E_4, 4*E_1-4*E_2}, {5*E_0-4*E_1-3*E_2-5*E_3, -2*E_0+4*E_4,
      -3*E_0+5*E_1+4*E_2, 3*E_1-3*E_2}},3,({1, 1, 1, 1, 2, 4},new Tally from {((2,1),(1,5)) => 1, ((2,1),(1,6)) =>
      5, ((3,1),(2,5)) => 1})), (matrix {{2*E_1-4*E_2+3*E_3, -E_1-3*E_2-2*E_4, -5*E_1-E_2, 2*E_1+5*E_2},
      {4*E_0+5*E_1-2*E_3, -3*E_0+E_1+3*E_2-3*E_4, -E_1+2*E_2, 3*E_1+2*E_2}, {-4*E_0+E_1+4*E_3, 3*E_0-4*E_4,
      -4*E_1-3*E_2, 4*E_2-E_3+E_4}},3,({1, 1, 1, 1, 2, 3},new Tally from {((2,1),(1,5)) => 1, ((2,1),(1,6)) => 5,
      ((3,1),(2,5)) => 1})), (matrix {{-2*E_0+3*E_1-4*E_2-3*E_3, 0, E_0-3*E_2+4*E_3+E_4, -5*E_0+5*E_1-2*E_3+2*E_4},
      {-E_0+2*E_1-2*E_2+2*E_3, 0, 3*E_0+5*E_2, -5*E_0+4*E_1-2*E_2-5*E_3+5*E_4}, {-3*E_0+5*E_2-3*E_3,
      -5*E_0+4*E_1-4*E_2, 4*E_0-2*E_2-2*E_3+5*E_4, 5*E_0-E_2-5*E_3+5*E_4}},5,({1, 1, 1, 1, 1, 7},new Tally from
      {((2,1),(1,5)) => 2, ((2,4),(1,23)) => 1, ((3,1),(2,5)) => 1}))};);
if o.Verbose then ( << "#mdKRs = " << #mdKRs <<endl);
     if not k <#mdKRs then (<<"only "|#mdKRs|" examples stored"<<flush<<endl;return ideal 1_(P4));
      mdKR:=mdKRs_k;
      if o.Verbose then (
      << "(K,R) = " << mdKR_2 <<", dim Hom = " <<mdKR_1 <<flush<<endl;);
      m3x4:= mdKR_0;
      X:=aboSurfaceFromMatrix(m3x4,P4);
      return X)




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

ellipticSurfaceD12S13=method()
-- Regular elliptic surface of degree 12 and sectional genus 13 obtained as the dependency locus of two global sections of an extension of the HM bundle (B7.7)
--     PURPOSE : Construct a nonsingular regular elliptic surface of degree 12 and sectional genus 13
--       INPUT : 'P4', the homogeneous coordinate ring of projective fourspace 
--      OUTPUT : Ideal of the elliptic surface
-- DESCRIPTION : This function constructs a regular elliptic surface as the dependency locus of two sections of a rank three vector bundle
--     COMMENT : This function uses the BGG package

ellipticSurfaceD12S13(PolynomialRing) := P4 -> (
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
    -- Construct 'X' as the degeneracy locus of a generic map from (15 O_P4(-2) ++ O_P4(-3))
    -- to the sheafified second syzygy module of the dual of 'sigma'
    X:=trim ideal syz(transpose (ff.dd_4 |random(target ff.dd_4,P4^{15:-2,-3})),DegreeLimit=>2);
    -- Check whether 'X' is a surface with the desired degree and sectional genus
    assert(dim X==3 and degree X==15 and sectionalGenus X==21);
    X)

K3surfaceD6=method()
-- K3 surface of degree 6 and sectional genus 4 
--     PURPOSE : Construct the (2,3) complete Intersection
--       INPUT : 'P4', the homogeneous coordinate ring of projective fourspace 
--      OUTPUT : Ideal of the K3 surface of degree 6
-- DESCRIPTION : This function constructs the K3 surface as a complete intersection (2,3)
K3surfaceD6(PolynomialRing):= P4 -> (
    -- the complete intersection (2,3) is a minimal K3 surface of degree 6 and sectional genus 4.
    X:=ideal random(P4^1,P4^{-2,-3});
    -- Check whether 'X' is a surface with the desired degree and sectional genus
    assert(dim X==3 and degree X==6 and sectionalGenus X==4);
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


K3surfaceD10S9L1=method()
-- K3 surface of degree 10 and sectional genus 9 with one 6-secant line (this script is a little cheating) (B4.6)
--     PURPOSE : Construct a nonsingular K3 surface of degree 10 and sectional genus 9 with one 6-secant line
--       INPUT : 'P4', the homogeneous coordinate ring of projective fourspace 
--      OUTPUT : Ideal of the K3 surface of degree 10 with one 6-secant line
-- DESCRIPTION : This function constructs the ideal of the K3 surface as the homology of a Beilinson monad
--     COMMENT : This function uses the BGG package

K3surfaceD10S9L1(PolynomialRing) := P4 -> (
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

K3surfaceD10S9L3=method()
K3surfaceD10S9L3(PolynomialRing) := P4 -> (
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

K3surfaceD11S11Ln=method()
-- K3 surface of degree 11 and sectional genus 11 witha 6-secant lines (B4.8-11)
--     PURPOSE : Construct a nonsingular K3 surface of degree 11 and sectional genus 11 with 'n' 6-secant lines
--       INPUT : 'P4', the homogeneous coordinate ring of projective fourspace and an integer between 0 and 3 
--      OUTPUT : Ideal of the K3 surface of degree 10 with 'n' 6-secant lines
-- DESCRIPTION : This function constructs the ideal of the K3 surface as the degeneracy locus of a map between two vector bundles
--     COMMENT : This function uses 'H1module,' a command that takes "P4' and an integer between 0 and 3 and returns the H1 module of the ideal sheaf of the surface 

K3surfaceD11S11Ln(PolynomialRing,ZZ):=(P4,n)->(
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


K3surfaceD11S12=method()
-- K3 surface of degree 11 and sectional genus 12 (B4.12)
--     PURPOSE : Construct a nonsingular K3 surface of degree 11 and sectional genus 12 
--       INPUT : 'P4', the homogeneous coordinate ring of projective fourspace 
--      OUTPUT : Ideal of the K3 surface of degree 11 and sectional genus 12
-- DESCRIPTION : This function constructs the K3 surface as the degeneracy locus of a map between two vector bundles

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


K3surfaceD12=method()
-- K3 surface of degree 12 and sectional genus 14 (B4.13)
--     PURPOSE : Construct a nonsingular K3 surface of degree 12 and sectional genus 14
--       INPUT : 'P4', the homogeneous coordinate ring of projective fourspace 
--      OUTPUT : Ideal of the K3 surface of degree 12 
-- DESCRIPTION : This function constructs the K3 surface as the surface residual to a regular elliptic surface of degree 12 in the (5,5) complete intersection
--     COMMENT : This function uses 'BGG'

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


K3surfaceD13=method()
-- K3 surface of degree 13 and sectional genus 16 (B4.14)
--     PURPOSE : Construct a nonsingular K3 surface of degree 13 and sectional genus 16
--       INPUT : 'P4', the homogeneous coordinate ring of projective fourspace 
--      OUTPUT : Ideal of the K3 surface of degree 13 
-- DESCRIPTION : This function constructs the K3 surface as the surface residual to a regular elliptic surface of degree 12 in the (5,5) complete intersection
--     COMMENT : This function uses 'regularEllipticSurfaceD12'

K3surfaceD13(PolynomialRing):=P4->(
    -- Use 'regularEllipticSurfaceD12'to construct a regular elliptic surface of degree 12
    Y:=ellipticSurfaceD12S13(P4);
    -- Choose two quintics containing 'Y' to define a complete intersection 'V' 
    V:=ideal ((gens Y)*random(source gens Y,P4^{2:-5}));
    -- Define 'X' resitual to 'Y' in 'V'
    X:=V:Y;
    -- Check whether 'X' is a surface with the desired degree and sectional genus
    assert(dim X==3 and degree X==13 and sectionalGenus X==16);
    X)


K3surfaceD14=method()
-- K3 surface of degree 14 and sectional genus 19 (B4.15)
--     PURPOSE : Construct a nonsingular K3 surface of degree 14 and sectional genus 19
--       INPUT : 'P4', the homogeneous coordinate ring of projective fourspace 
--      OUTPUT : Ideal of the K3 surface of degree 14
-- DESCRIPTION : This function constructs the K3 surface as the degeneracy locus of a map between two vector bundles

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


ellipticSurfaceD7=method()
-- Elliptic surface of degree 7 and sectional genus 6 (B7.1)
--     PURPOSE : Construct a nonsingular elliptic surface of degree 7 and sectional genus 6
--       INPUT : 'P4', the homogeneous coordinate ring of projective fourspace 
--      OUTPUT : Ideal of the elliptic surface of degree 7
-- DESCRIPTION : This function constructs the elliptic surface as the degeneracy locus of a map between two vector bundles

ellipticSurfaceD7(PolynomialRing) := P4 -> (
    -- Construct 'X' as the dependency locus of a generic map from 2O_P4(-2) to 2O_P4(-1) ++ O_P4(1)  
    X:=minors(2,random(P4^{1:1,2:-1},P4^{2:-2}));
    -- Check whether 'X' is a surface with the desired degree and sectional genus
    assert(dim X==3 and degree X==7 and sectionalGenus X==6);
    X)


ellipticSurfaceD8=method()
-- Elliptic surface of degree 8 and sectional genus 7 (B7.2)
--     PURPOSE : Construct a nonsingular elliptic surface of degree 8 and sectional genus 7
--       INPUT : 'P4', the homogeneous coordinate ring of projective fourspace 
--      OUTPUT : Ideal of the elliptic surface of degree 8
-- DESCRIPTION : This function constructs the elliptic surface as the degeneracy locus of a map between two vector bundles

ellipticSurfaceD8(PolynomialRing) := P4 -> (
    -- Construct 'X' as the dependency locus of a generic map from 2O_P4(-2) to O_P4 ++ 2O_P4(1)  
    X:=minors(2,random(P4^{2:1,1:0},P4^{2:-1}));
    -- Check whether 'X' is a surface with the desired degree and sectional genus
    assert(dim X==3 and degree X==8 and sectionalGenus X==7);
    X)


ellipticSurfaceD9=method()
-- Elliptic surface of degree 9 and sectional genus 7 (B7.3)
--     PURPOSE : Construct a nonsingular elliptic surface of degree 9 and sectional genus 7
--       INPUT : 'P4', the homogeneous coordinate ring of projective fourspace 
--      OUTPUT : Ideal of the elliptic surface of degree 9
-- DESCRIPTION : This function constructs the elliptic surface
--               as the degeneracy locus of a map between avector bundle and a sum of line bundles
--     COMMENT : This function uses the BGG package

ellipticSurfaceD9(PolynomialRing) := P4 -> (
   --desired H1-module
   H1:=coker random(P4^{2:-2},P4^{7:-3});
   fH1:=res( H1,LengthLimit=>2);
   -- toString betti fH1
   A:=syz transpose (fH1.dd_2*random(source fH1.dd_2,P4^{3:-4,-5}));
   X:=trim ideal (transpose A_{2}*fH1.dd_2); 
    -- Check whether 'X' is a surface with the desired degree and sectional genus
    assert(dim X==3 and degree X==9 and sectionalGenus X==7);
    X)



ellipticSurfaceD10S9=method()
-- Elliptic surface of degree 10 and sectional genus 9 (B7.4)
--     PURPOSE : Construct a nonsingular elliptic surface of degree 10 and sectional genus 9
--       INPUT : 'P4', the homogeneous coordinate ring of projective fourspace 
--      OUTPUT : Ideal of the elliptic surface of degree 9
-- DESCRIPTION : This function constructs the elliptic surface as the homology of a Beilinson monad 
--     COMMENT : This function uses the BGG package

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
    

ellipticSurfaceD10S10=method()
-- Elliptic surface of degree 10 and sectional genus 10 (B7.5)
--     PURPOSE : Construct a nonsingular elliptic surface of degree 10 and sectional genus 10
--       INPUT : 'P4', the homogeneous coordinate ring of projective fourspace 
--      OUTPUT : Ideal of the elliptic surface of degree 10
-- DESCRIPTION : This function constructs the elliptic surface as the degeneracy locus of a map between two vector bundles
--     COMMENT : This function uses the BGG package

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


ellipticSurfaceD11S12=method()
-- Elliptic surface of degree 11 and sectional genus 12 (B7.6)
--     PURPOSE : Construct a nonsingular elliptic surface of degree 11 and sectional genus 12
--       INPUT : 'P4', the homogeneous coordinate ring of projective fourspace 
--      OUTPUT : Ideal of the elliptic surface of degree 10
-- DESCRIPTION : This function constructs the elliptic surface as the degeneracy locus of a map between two vector bundles
--     COMMENT : This function uses the BGG package

ellipticSurfaceD11S12(PolynomialRing):= P4 -> (
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



ellipticSurfaceD12S14L0=method()
-- Elliptic surface of degree 12 and sectional genus 14 with no 6 secant line (B7.8)
--     PURPOSE : Construct a nonsingular elliptic surface of degree 12 and sectional genus 14
--       INPUT : 'P4', the homogeneous coordinate ring of projective fourspace 
--      OUTPUT : Ideal of the elliptic surface of degree 12
-- DESCRIPTION : This function constructs the elliptic surface as the homology of a Beilinson monad 
--     COMMENT : This function uses the BGG package
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


ellipticSurfaceD12S14Linfinite=method()
-- Elliptic surface of degree 12 and sectional genus 14 with infinitely many 6 secant line (B7.9)
--     PURPOSE : Construct a nonsingular elliptic surface of degree 12 and sectional genus 14 with infinitely many 6-secant lines
--       INPUT : 'P4', the homogeneous coordinate ring of projective fourspace 
--      OUTPUT : Ideal of the elliptic surface of degree 12
-- DESCRIPTION : This function constructs the elliptic surface as the homology of a Beilinson monad 
--     COMMENT : This function uses the BGG package

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

specificEllipticSurfaceD13S16=method(Options=>{Verbose=>false})

specificEllipticSurfaceD13S16(PolynomialRing,Ring,ZZ):= o -> (P4,E,k) -> (
    if not member(k,{1,2,4,6}) then (<< k <<" should be in "<<{1,2,4,6} <<flush<<endl;
	    return ideal 1_P4);
    X:=specificAboSurface(P4,E,k,Verbose=>o.Verbose);
    betti(ci:=ideal(gens X*random(source gens X,P4^{2:-5})));
    Y:=ci:X;
    return Y)
///



kk=ZZ/19
P4=kk[x_0..x_4]
E=kk[e_0..e_4,SkewCommutative=>true]
Y=specificAboSurface(P4,E,1,Verbose=>true);
X=specificEllipticSurfaceD13S16(P4,E,1);
betti tateResolutionOfSurface X
(d,sg)=(degree X, sectionalGenus X)
LeBarzN6(d,sg,3)
R=residualInQuintics X;
cR=decompose R;
tally apply(cR,c->(dim c, degree c,(dim(c+X),degree (c+X))))

Y=specificAboSurface(P4,E,2,Verbose=>true);
X=specificEllipticSurfaceD13S16(P4,E,2);
R=residualInQuintics X;
cR=decompose R;
tally apply(cR,c->(dim c, degree c,(dim(c+X),degree (c+X))))

Y=specificAboSurface(P4,E,4,Verbose=>true);
X=specificEllipticSurfaceD13S16(P4,E,4);
R=residualInQuintics X;
cR=decompose R;
tally apply(cR,c->(dim c, degree c,(dim(c+X),degree (c+X))))

Y=specificAboSurface(P4,E,6,Verbose=>true);
RY=residualInQuintics Y;
tally apply(decompose RY,c->(dim c, degree c,(dim(c+Y),degree (c+Y))))
X=specificEllipticSurfaceD13S16(P4,E,6);
betti tateResolutionOfSurface X
(d,s)=(degree X, sectionalGenus X)
Ksquare(d,s,3)
D=canonicalDivisor X;
degree D
degree RY
E=D:RY;
(dim E,degree E,genus E,selfIntersectionNumber(X,E))
cD=decompose D;
tally apply(cD,c->(dim c, degree c, genus c, selfInterSectionNumber(X,c)))
R=residualInQuintics X;
cR=decompose R;
tally apply(cR,c->(dim c, degree c,(dim(c+X),degree (c+X))))

///

///
kk=ZZ/19
P4=kk[x_0..x_4]
E=kk[e_0..e_4,SkewCommutative=>true]
X=specificAboSurface(P4,E,1);
betti(ci=ideal(gens X*random(source gens X,P4^{2:-5})))
minimalBetti (Y=ci:X)
betti tateResolutionOfSurface Y
dim singularLocus Y
K1=canonicalDivisor Y;
K2=canonicalDivisor Y;
betti(baseLocus=saturate (K1+K2))
E1=K1:baseLocus;
dim E1, degree E1, genus E1, selfIntersectionNumber(Y,E1)
betti(baseLocus1=K1:E1)
cBaseLocus1=decompose baseLocus1;
tally apply(cBaseLocus1,c->(dim c, degree c, genus c, selfIntersectionNumber(Y,c)))
Ksquare(13,16,3)
///


/// -* rank 2 vector bundle on P4 *-
R=QQ[a,b,c1,c2]
binom=c -> product(4,i->(c+(i+1))/(i+1))
binom a
(a+4)*(a+3)*(a+2)*(a+1)
xEnd=binom(a-b)+binom(b-a)+2*binom 0
rel=ideal(a+b-c1,a*b-c2)
xEnd1=xEnd%rel
h1minush2End=1-sub(xEnd1,{c1=>-1,c2=>4})
h1minush2End=1-sub(xEnd1,{c1=>0,c2=>11})
///

searchHMBundle=method()
--Input: exterior algebra dual to P4
--       over s small finite prime field, e.g. kk=ZZ/2
searchHMBundle(Ring,ZZ) := (E,c) -> (
    p:=char E;
    Cs:={};
    N:=0;M:=0;trials:= 0;
    A:=null; B:=null; B1 :=null; C:=null;
    fC:=null;
    count:=0;
    while(N<2^c and #Cs<1) do ( 
	while (A=random(E^3,E^{2:-2});
	    betti (B=syz(A,DegreeLimit=>5));
	    B1=(B*random(source B, E^{5:-4}));
	    rank source (syz(B1,DegreeLimit=>4))!=0) do (trials=trials+1);
	betti (C=syz(transpose B1,DegreeLimit=>0));
	N=N+1;
	betti (fC=res(coker transpose C,LengthLimit=>2));
	if rank fC_0==5 and rank fC_2==5 then (
	    M=M+1;fC=res(coker transpose C,LengthLimit=>4);
	    if rank fC_4 <=14 then (print N;Cs=append(Cs,C)));
	);
    << "number of trials = " <<trials <<endl;
    << "(N,M) = " <<(N,M) <<endl;
    Cs)



varietyOfUnstablePlanes=method(Options=>{Verbose=>1})

varietyOfUnstablePlanes(Matrix) := o -> m2x5 -> (
    E:= ring m2x5;
    kk:=coefficientRing E;
    p:=symbol p;
    P:=kk[p_0..p_9];
    m5x5:=genericSkewMatrix(P,p_0,5);
    EP:=E**P;
    J:=ideal apply(subsets(toList(0..4),2),ij->(i:=ij_0;j:=ij_1;
	sub(E_i*E_j,EP) - sub(m5x5_(i,j),EP)));
    m5x2P:=sub(sub(transpose m2x5,EP)%J,P);
    s:= symbol s;t := symbol t; x := symbol x;
    P1xP4:=kk[s,t,x_0..x_4,Degrees=>{2:{1,0},5:{0,1}}];
    m5x2P1xP4:=matrix apply(5,i->apply(2,j->P1xP4_j*x_i));
    PP14:=P**P1xP4;
    J2:=ideal(sub(m5x2P,PP14)-sub(m5x2P1xP4,PP14));
    m5x5P1xP4:=sub(sub(m5x5,PP14)%J2,P1xP4);
    I:=pfaffians(4,m5x5P1xP4);
    Is:=saturate(saturate(I,ideal(P1xP4_0,P1xP4_1)),ideal apply(5,i->P1xP4_(i+2)));
    dim Is == 2+2;
    xx:=matrix{apply(5,i->P1xP4_(i+2))};
    betti(relativeJacobian:=diff(transpose xx,gens I));
    betti(singFibs:=saturate(minors(3,relativeJacobian)+I,ideal xx));
    if o.Verbose >1 then (
	<<"singularFibers = " <<factor singFibs_30 <<endl);   
    kk':=GF(char kk,8);
    P1xP4':=kk'[gens P1xP4,Degrees=>degrees P1xP4];
    P4':=kk'[x_0..x_4];
    csingFibs:=decompose  ideal sub(singFibs_30,P1xP4');
    singFibers:=apply(csingFibs,c->trim sub(saturate(c+sub(I,P1xP4'),ideal(P1xP4'_1,P1xP4'_0)),P4'));
    elapsedTime sortedComponentsPlusImats:=apply(singFibers,c->(
	cc:=decompose c;iMat:=matrix apply(cc,d1->apply(cc,d2->
		if d1 != d2 then degree saturate(d1+d2) else 0));
	cycle:={0};
	scan(4,s->(
	cycle=append(cycle,first select(select(toList(0..4),j->not member(j,cycle)),
		j->iMat_(last cycle,j)==1))));
        (cc_cycle,iMat^cycle_cycle)));
     if o.Verbose >0 then (
	 <<"number of components and intersection matrices = "
	 <<tally apply(sortedComponentsPlusImats,cc->(
	    (#cc_0,diagonalMatrix toList(5:-2)+cc_1)))<<endl;
    
<<"-- => the singular fibers consists of 12 pentagons of lines.
-- => the surface of unstable plane of the bundle coincides with Shioda's modular surface
-- => the bundle is projectively equivalent to the HM bundle"<<endl;);
   sortedComponents:= apply(sortedComponentsPlusImats,cc->cc_0);
   pointsIdeals:=apply(sortedComponents,cc->intersect(apply(4,i->cc_i+cc_(i+1))|{cc_4+cc_0}));
   if o.Verbose>0 then (
       <<"number and betti table of singular points = "
       <<tally apply(pointsIdeals,p->(degree p, betti res p)) <<endl;
       <<"pairs of singular fibers = "
       <<unique apply(pointsIdeals,p0->positions(pointsIdeals,p->p==p0)) <<endl;
       );
    sortedComponents) 

///
p=2
kk=ZZ/p
E=kk[e_0..e_4,SkewCommutative=>true]
13752.3/60/60 --for 2^21
setRandomSeed("run 2^12")
c=12
elapsedTime MCs=searchHMBundle(E,c)
///
    
-* Documentation section *-


beginDocumentation()


document {
Key => NongeneralTypeSurfacesInP4,
Headline => "Construction of smooth non-general type surfaces in P4",
   "In 1989, Elligsrud and Peskine proved a conjecture of Hartshorne and Lichtenbaum about smooth rational surfaces in P4. In fact, more general:
    There are only finitely many components of the Hilbert scheme of surfaces in P4, whose general point corresponds to a smooth 
    surface not of general type.

   During that period, there was a flourish of activities to construct such surfaces, in part using Computer Algebra. In this package we review
   those constructions, which, after 30 years of Macaulay2, have become simpler and faster. Moreover, we have discovered a few further 
   examples.",

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
	TO irregularEllipticSurfaceD12,
        },
    SUBSECTION "Elliptic surfaces",
     UL{
        TO irregularEllipticSurfaceD12,
	TO surfacesOfKodairaDimension1,
        },
     SUBSECTION "Investigating embedded surfaces",
     UL{
	TO adjunctionProcessData,
	TO residualInQuintics,
	TO canonicalDivisor,
	TO selfIntersectionNumber,
	TO tateResolutionOfSurface,
	TO numericalFunctions,
        },
    PARA{},

}

document {
Key => unirationalFamiliesOfRationalSurfaces,
Headline => "unirational families of rational surfaces",
   "Most of the families constructed in [DES], [Popescu1] and earlier are actually unirational. We list the links to the corresponding functions.
    Exceptions are certain families of Schreyer and Abo-Ranestad surfaces, where we only know that some of the families are unirational.",
   
   PARA{},
     SUBSECTION "non-degenerate rational surfaces in P4",
     UL{
        TO cubicScroll,
	TO delPezzoSurface,
	TO castelnuovoSurface,
	TO bordigaSurface,        
        TO ionescuOkonekSurfaceD7,
	TO okonekSurfaceD8S6,
	TO ionescuOkonekSurfaceD8S5,
	TO nonspecialAlexanderSurface,--
	TO specialityOneAlexanderSurface,--
	TO degree10DESSurface,--
	TO degree10pi9RanestadSurface,--
	TO degree10pi8RanestadSurface,--
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
Key => numericalFunctions,
Headline => "Various numerical functions to investigate surfaces in P4",
   
   PARA{},
     SUBSECTION "Intersection numbers",
     UL{
        TO LeBarzN6,
	TO Ksquare,
        TO HdotK,
	TO sectionalGenus,
        },
    
     SUBSECTION "Tate resolutions",
     UL{
	TO tateResolutionOfSurface,
        TO chiITable,
	TO chiO,
	TO irregularity,
	TO geometricGenus,        
        },

    SUBSECTION "6-secants and canonical divisors",
     UL{
	TO canonicalDivisor,
        TO partitionOfCanonicalDivisorOfAboSurface,
	TO residualInQuintics,      
        },
    
   
}



document {
Key => schreyerSurfaces,
Headline => "functions concerning Schreyer surfaces (8 families)",
   "[Schreyer,1996] discovered 4 families of surfaces X in P4 with d=11 and sectional genus pi=10 via a search over a finite field
   of which 3 families consist of rational surfaces. 
   Repeating such search now, we found altogether 8 families of rational surfaces and 1 family of Enriques surfaces. 
   In the following, we give an overview of the functions used in that search.",
   
   PARA{},
     SUBSECTION "From modules to surfaces",
     UL{
        TO schreyerSurfaceFromModule,
	TO moduleFromSchreyerSurface,
        TO exampleOfSchreyerSurfaces,
        TO specificSchreyerSurface
        },
    
     SUBSECTION "Search for modules",
     UL{
        TO findRandomSmoothSchreyerSurface, 
        TO collectSchreyerSurfaces
        },
    
     SUBSECTION "Lift to characteristic zero and unirational or nearly unirational families",
     UL{
	TO tangentDimension,
	TO specialEnriquesSchreyerSurface, 
	TO schreyerSurfaceWith2LinearSyzygies,
	TO schreyerSurfaceWith2or3LinearSyzygies,
        }        
}



document {
Key => aboRanestadSurfaces,
Headline => "functions concerning Abo-Ranestad surfaces (7 families)",
   "[Abo-Ranestad,2006] discovered 4 families of rational surfaces X in P4 with d=12 and sectional genus pi=13 via a search over a finite field.
    Reviewing their construction we found altogether 7 families. 
    Most of these components are unirational.",
   
   PARA{},
     SUBSECTION "From matrices to surfaces",
     UL{
        TO aboRanestadSurfaceFromMatrix,
	TO matrixFromAboRanestadSurface       
        },
    
     SUBSECTION "Search for modules",
     UL{
	TO aboRanestadSurface,
	TO specificAboRanestadSurface,
	TO get4x2Matrix,
        },
    
     SUBSECTION "Lift to characteristic zero",
     UL{
	TO veroneseImagesInG25
        }        
}

document {
Key => K3surfaces,
Headline => "Known families of K3 surfaces",
   "Various families of non-minmal K3 surfaces are known.
    We enumerate the families by the degree D, the sectional genus S, and
    their 6-secant behavior L. Note that a smooth surface in P4 is expected to have 
    finitely many 6-secants. If this number is finite, then Le Barz' 6-secant formula
    computes the sum of the number of 6-secants and the number of  of (-1) lines on the surface.
    Since every 6-secant line is contained in the zero locus of the ideal generated by the quintics
    containing the surface, the number of 6-secants can often be determined from the equation
    of the surface. In that case we get information about the (-1)-Lines, i.e. ,
    the curve contracted by the first adjunction map.",
    
   PARA{},
     SUBSECTION "K3 surfaces",
     UL{
	TO K3surfaceD6,
        TO K3surfaceD7,
	TO K3surfaceD8,
	TO K3surfaceD9,
	TO K3surfaceD10S9L1,
	TO K3surfaceD10S9L3,
	-- TO H1module,
	TO K3surfaceD11S11Ln,
	TO K3surfaceD11S12,
	TO K3surfaceD12,
	TO K3surfaceD13,
	TO K3surfaceD14,
	TO aboSurfaces,
        },
    PARA{},
     SUBSECTION "6-secants and adjunction",
     UL{
	TO LeBarzN6,
	TO residualInQuintics,
	TO canonicalDivisor,
	TO partitionOfCanonicalDivisorOfAboSurface,
	TO selfIntersectionNumber,
	},
}

document {
Key => aboSurfaces,
Headline => "functions for investigating Abo surfaces, (9 families)",
   "A regular smooth surface X of degree 12, sectional genus 13 and Euler 
characteristic 2 has a Tate resolution for the ideal sheaf o shape",

    
   PARA{},
     SUBSECTION "K3 surfaces of degree 12 and sectional genus 13",
     UL{
	TO aboSurfaceFromMatrix,
        TO testMatrix1,
	TO testMatrix2,	
	TO randomAboSurface,
	TO analyzeAboSurface,
	TO collectAboSurfaces,
	TO specificAboSurface,
	TO abo112224Or111234Surface,
        },
    PARA{},
     SUBSECTION "Unirational or nearly unirational constructions",
     UL{
	TO abo111333Surface,
	TO abo111144Surface,
	TO abo111117Surface,
	},
    PARA{},
     SUBSECTION "6-secants and adjunction",
     UL{
	TO LeBarzN6,
	TO residualInQuintics,
	TO canonicalDivisor,
	TO partitionOfCanonicalDivisorOfAboSurface,
	TO selfIntersectionNumber,
	},
}

document {
Key => surfacesOfKodairaDimension1,
Headline => "surface of Kodaira dimension 1 (15 families)",
   "",
    
   PARA{},
     SUBSECTION "elliptic surfaces",
     UL{	
        TO ellipticSurfaceD7,
	TO ellipticSurfaceD8,
	TO ellipticSurfaceD9,
	TO ellipticSurfaceD10S9,
	TO ellipticSurfaceD10S10,
	TO ellipticSurfaceD11S12,
	TO ellipticSurfaceD12S14L0,
	TO ellipticSurfaceD12S14Linfinite,
	TO ellipticSurfaceD12S13,
	TO irregularEllipticSurfaceD12,	
	TO specificEllipticAboSurfaceD12S13,	
	TO specificEllipticSurfaceD13S16,
        },
    PARA{},
     SUBSECTION "6-secants and adjunction",
     UL{
	TO LeBarzN6,
	TO residualInQuintics,
	TO canonicalDivisor,
	TO selfIntersectionNumber,
	},
}

document {
Key => adjunctionProcessData,
Headline => "explains the output of the function adjunctionProcess",
    "We explain the output of the function adjunctionProcess from the package adjunctionForSurfaces. 
    Notice the typo: adjointMatrix should be adjunctionProcess.",
help adjunctionProcess,                
}

document {
Key => symExtFunction,
Headline => "symExt",
    "documentation of the symExt function from the BGG package",
help symExt,                
}

-- numerical functions
 -*
  Example 
restart
needsPackage "NongeneralTypeSurfacesInP4"   
    chiITable(11,10,1)
    chiITable(12,13,1)
    chiITable(12,13,2)
    B=chiITable(12,13,3)    
    kk=ZZ/nextPrime 10^4
    P4=kk[x_0..x_4]
    X=ellipticSurfaceD12S13 P4;
    (degree X,sectionalGenus X)
    B'=betti tateResolutionOfSurface(X,7)
    B==B'
    keyWithZeroValue=select(keys B,k->not member(k,keys B'))
    B#(keyWithZeroValue_0)
  *-  
doc///
Key
 chiITable
 (chiITable,ZZ,ZZ,ZZ)
Headline
 compute a plausible cohomology tally for a smooth surface in P4
Usage
 B = chiITable(d,sg,xO)
Inputs
 d:ZZ
  a desired degree
 sg:ZZ
  a desired sectional genus
 xO:ZZ
  a desired Euler characteristic of O_X
Outputs
  B:BettiTally
    plausible Betti tally of the cohomology of the desired ideal sheaf
Description
  Text
    Since

    chi(I_X(m))=chi(O_P4(m))-chi(O_X(m))

    one can compute chi(I_X(m)) using Riemann-Roch which depends only
    degree d, the sectional genus sg, the Euler characteristic xO and m.
    Assuming that I_X has natural cohomology for m in {-4..8} and that m -> chi(I_X(m)) has enough
    sign changes, we get a plausible table.
  CannedExample
    i2 : chiITable(11,10,1)

                 -1  0  1  2 3 4  5  6  7   8
    o2 = total: 104 61 30 10 3 5 10 32 84 170
            -4:   1  .  .  . . .  .  .  .   .
            -3: 103 61 30 10 . .  .  .  .   .
            -2:   .  .  .  . 2 .  .  .  .   .
            -1:   .  .  .  . 1 5  5  .  .   .
             0:   .  .  .  . . .  5 32 84 170

     o2 : BettiTally

     i3 : chiITable(12,13,1)

                  -1  0  1  2 3 4 5  6  7   8
     o3 = total: 122 73 37 13 4 4 8 29 77 158
             -4:   1  .  .  . . . .  .  .   .
             -3: 121 73 37 13 . . .  .  .   .
             -2:   .  .  .  . 4 2 .  .  .   .
             -1:   .  .  .  . . 2 3  .  .   .
              0:   .  .  .  . . . 5 29 77 158

     o3 : BettiTally

     i4 : chiITable(12,13,2)
 
                  -1  0  1  2 3 4 5  6  7   8
     o4 = total: 123 74 38 14 4 4 8 28 76 157
             -4:   1  .  .  . . . .  .  .   .
             -3: 122 74 38 14 1 . .  .  .   .
             -2:   .  .  .  . 3 1 .  .  .   .
             -1:   .  .  .  . . 3 4  .  .   .
              0:   .  .  .  . . . 4 28 76 157

     o4 : BettiTally

     i5 : B=chiITable(12,13,3)    

                  -1  0  1  2 3 4 5  6  7   8
     o5 = total: 124 75 39 15 4 4 8 27 75 156
             -4:   1  .  .  . . . .  .  .   .
             -3: 123 75 39 15 2 . .  .  .   .
             -2:   .  .  .  . 2 . .  .  .   .
             -1:   .  .  .  . . 4 5  .  .   .
              0:   .  .  .  . . . 3 27 75 156

     o5 : BettiTally

     i6 : kk=ZZ/nextPrime 10^4

     o6 = kk

     o6 : QuotientRing

     i7 :     P4=kk[x_0..x_4]

     o7 = P4

     o7 : PolynomialRing

     i8 : X=ellipticSurfaceD12S13 P4;

     o8 : Ideal of P4

     i9 : (degree X,sectionalGenus X)

     o9 = (12, 13)

     o9 : Sequence

     i10 : B'=betti tateResolutionOfSurface(X,7)

                   -1  0  1  2 3 4 5  6  7   8
     o10 = total: 124 75 39 15 4 4 8 27 75 156
              -4:   1  .  .  . . . .  .  .   .
              -3: 123 75 39 15 2 . .  .  .   .
              -2:   .  .  .  . 2 . .  .  .   .
              -1:   .  .  .  . . 4 5  .  .   .
               0:   .  .  .  . . . 3 27 75 156

     o10 : BettiTally

     i11 :     B==B'

     o11 = false

     i12 :     keyWithZeroValue=select(keys B,k->not member(k,keys B'))

     o12 = {(4, {2}, 2)}

     o12 : List

     i13 : B#(keyWithZeroValue_0)

     o13 = 0
  Text
    If chi(I_X(m))\in ZZ[m] has an integral zero then B contains a superflous key.   
SeeAlso
   tateResolutionOfSurface
   ellipticSurfaceD12S13
   sectionalGenus
   chiO
///
///
chiITable(10,8,1)
tex chiITable(10,8,1)
chiITable(16,22,1)
apply(toList(-4..10),i->chiI(i,16,24,1))
chiITable(13,14,1)
chiITable(13,15,1)
p=7
kk=ZZ/p
E=kk[e_0..e_4,SkewCommutative=> true]
P4=kk[x_0..x_4]
while( --distinct values
    as=apply(5,i->random kk);
    #unique as != 5) do ()
m2x5=transpose matrix apply(5,i->{e_i,(i+1)*e_i})
elapsedTime tally apply(p^3,c->(	 
	m5x3=random(E^5,E^{3:-1});
	betti(hom=Hom(coker m2x5,coker m5x3,DegreeLimit=>4))))
///

doc///
Key
 sectionalGenus
 (sectionalGenus, Ideal)
Headline
 compute the sectional genus of a surface
Usage
 sg = sectionalGenus X
Inputs
 X:Ideal
  ideal of a (smooth) projective surface
Outputs
 sg:ZZ
  the genus of a hyperplane section
Description
  Text
    The sectional genus of a projective surface is a part of the data provided by
    the function genera.
  Example
    kk=ZZ/nextPrime 10^4
    P4=kk[x_0..x_4]
    X=bordigaSurface P4;
    sectionalGenus X
    genera X
    degree X == last genera X +1
SeeAlso
   genera
///

doc///
Key
 HdotK
 (HdotK, ZZ,ZZ)
Headline
 compute the intersection number H.K 
Usage
 HK = HdotK(d,sg)
Inputs
 d:ZZ
  degree of a smooth projective surface
Outputs
 sg:ZZ
  the genus of a hyperplane section
Description
  Text
    Let H denote the hyperplane class and K the canonical divisor class on a smooth projective surface.
    By the adjunction formula

    2sg-2=H.(H+K)

    one can compute H.K from the degree d=H.H and the sectional genus sg.
  Example
    kk=ZZ/nextPrime 10^4
    P4=kk[x_0..x_4]
    X=bordigaSurface P4;
    d=degree X
    sg=sectionalGenus X
    HdotK(d,sg)   
SeeAlso
   sectionalGenus
///


doc///
Key
 Ksquare
 (Ksquare,ZZ,ZZ,ZZ)
Headline
 compute the self intersection number K^2 of a smooth surface X in P4.
Usage
 k2 = Ksquare(d,sg,xO)
Inputs
 d:ZZ
  the degree of X
 sg:ZZ
  the sectional genus of X
 xO:ZZ
  the Euler charcteristic (1-q+pg) of O_X
Outputs
 k2:ZZ

Description
  Text
   The self-intersection number of the canonical divisor of a smooth surface in P4
   is determined by the degree d, the sectional genus and the Euler characteristic
   of chi(O_X)=h^0(O_X)-h^1(O_X)+h^2(O_X):
  
      d^2-10d-5HK+2K2+12chi(O_X)==0

   In general for a surface in P5 the right-hand side in this formula gives
   the number of non Cohen-Macaulay double points of the image under a projection from a
   point p in P5 \setminus X. Hence the name.
  Example
    kk=ZZ/nextPrime 10^4
    P4=kk[x_0..x_4]
    X=bordigaSurface P4;
    d=degree X
    sg=sectionalGenus X
    HK=HdotK(d,sg)
    xO=1+(genera X)_0
    xO==chiO(X)
    K2=Ksquare(d,sg,xO)
    d^2-10*d-5*HK-2*K2+12*xO==0
  Text
    The complete intersection of a quadric and a cubic in P4 is a minimal
    K3 surface.
  Example
    X=ideal random(P4^1,P4^{-2,-3});
    d=degree X
    sg=sectionalGenus X
    HK=HdotK(d,sg)
    xO=1+(genera X)_0
    xO==chiO(X)
    K2=Ksquare(d,sg,xO)
    d^2-10*d-5*HK-2*K2+12*xO==0
References
   \textit{Hartshorne, R.}, Algebraic Geometry , GTM 52, Springer (1977), Appendix A
SeeAlso
   HdotK
   sectionalGenus
   chiO
   irregularity
   geometricGenus
///

doc///
Key
 chiO
 (chiO,Ideal)
Headline
 compute the Euler characteristic chiO(X)
Usage
 xO = chiO(X)
Inputs
 X:Ideal
  of a smooth projective variety
Outputs
 xO:ZZ
  the Euler characteristic of the strucure sheaf
Description
  Text
   The Euler characteristic of the structure sheaf O_X is

     chi(O_X)=sum_{i=0}^{dim X} (-1)^i*h^i(O_X).
  
   This quantity coincides with 1+ (genera X)_0 by the Hirzebruch-Riemann-Roch Theorem.
  Example
    kk=ZZ/nextPrime 10^4
    P4=kk[x_0..x_4]
    X=bordigaSurface P4;
    xO=chiO(X)
    xO=1+(genera X)_0
    q=irregularity X
    pg=geometricGenus X
    1-q+pg==chiO(X)
References
   \textit{Hartshorne, R.}, Algebraic Geometry , GTM 52, Springer (1977)
SeeAlso
   irregularity
   geometricGenus
///


-* for CannedExample irregularity
  Example
    kk=ZZ/nextPrime 10^4
    P4=kk[x_0..x_4]
    X=irregularEllipticSurfaceD12 P4;
    elapsedTime q=irregularity X
    pg=1+(genera X)_0
    elapsedTime 1-q+pg==chiO(X)
*-
doc///
Key
 irregularity
 (irregularity,Ideal)
Headline
 compute h^1(O_X)
Usage
 q = irregularity X
Inputs
 X:Ideal
  of a smooth projective surface
Outputs
 q:ZZ
  the dimension of the cohomology group H^1(O_X)
Description
  Text
    Using sheaf cohomology, we can compute the irregularity for a smooth projective surface.    
  CannedExample
    i1 : kk=ZZ/nextPrime 10^4

    o1 = kk

    o1 : QuotientRing
    i2 : P4=kk[x_0..x_4]

    o2 = P4

    o2 : PolynomialRing
    i3 : X=irregularEllipticSurfaceD12 P4;

    o3 : Ideal of P4
    i4 : elapsedTime q=irregularity X
    -- .00806553s elapsed

    o4 = 1
    i5 : pg=1+(genera X)_0

    o5 = 3
    i6 : elapsedTime 1-q+pg==chiO(X)
    -- .613765s elapsed

    o6 = true
References
   \textit{Hartshorne, R.}, Algebraic Geometry , GTM 52, Springer (1977)
SeeAlso
   chiO
   geometricGenus
///
-* for CannedExample geometricGenus
Example
    kk=ZZ/nextPrime 10^4
    P4=kk[x_0..x_4]
    X=irregularEllipticSurfaceD12 P4;
    elapsedTime pg=geometricGenus X
    elapsedTime xO=chiO(X)
    elapsedTime xO=1+(genera X)_0
    elapsedTime q=irregularity X   
    1-q+pg==chiO(X)
*-
doc///
Key
 geometricGenus
 (geometricGenus,Ideal)
Headline
 compute h^2(O_X)
Usage
 pg = geometricGenus
Inputs
 X:Ideal
  of a smooth projective surface
Outputs
 pg:ZZ
  the dimension of the cohomology group H^2(O_X)
Description
  Text
    Using sheaf cohomology,' we can compute this quantity for a smooth projective surface.
    It is alsop possible to use the function genera, which might be faster.
  CannedExample
    i1 : kk=ZZ/nextPrime 10^4

    o1 = kk

    o1 : QuotientRing
    i2 : P4=kk[x_0..x_4]

    o2 = P4

    o2 : PolynomialRing
    i3 : X=irregularEllipticSurfaceD12 P4;

    o3 : Ideal of P4
    i4 : elapsedTime pg=geometricGenus X
    -- .019619s elapsed

    o4 = 3
    i5 : elapsedTime xO=chiO(X)
    -- .580544s elapsed

    o5 = 3
    i6 : elapsedTime xO=1+(genera X)_0
    -- .000721903s elapsed

    o6 = 3
    i7 : elapsedTime q=irregularity X
    -- .0048388s elapsed

    o7 = 1
    i8 : 1-q+pg==chiO(X)

    o8 = true
  
References
   \textit{Hartshorne, R.}, Algebraic Geometry , GTM 52, Springer (1977), V
SeeAlso
   chiO
   irregularity
   genera
   tateResolutionOfSurface
///

-* for CannedExample in residualInQuintics
  Example
    kk=ZZ/nextPrime 10^4
    P4=kk[x_0..x_4]
    X=vBELSurface P4;
    d=degree X
    sg=sectionalGenus X
    xO=1+(genera X)_0
    N6=LeBarzN6(d,sg,xO)
    minimalBetti X
    Z=residualInQuintics X;
    dim Z, degree Z
    tally apply(decompose Z,L->(dim L, degree L, degree (L+X)))
  Text
    Thus, there are two 6-secant lines and by Le Barz' 6-secant formula,
    the first adjunction map defined by
    |H+K| contracts five (-1)-lines.    
  Example
    K2=Ksquare(d,sg,xO)
    elapsedTime (numList,L2,L3,J)=adjunctionProcess(X,2);
    numList=={(4, 11, 11), 5, (10, 18, 9), 14, (8, 8, 1)}
    degree J == 9-1
    minimalBetti J
    sectionalGenus J==1
    K2+5+14==9-1  

*-

doc///
Key
 LeBarzN6
 (LeBarzN6,ZZ,ZZ,ZZ)
Headline
 compute the value of Le Barz' formula for 6-secants lines
Usage
 N6 = LeBarzN6(d,sg,xO)
Inputs
 d:ZZ
  degree of a a smooth projective surface in P4
 sg:ZZ
  the sectional genus of X
 oX:ZZ
  the Euler characteristic of the structure sheaf
Outputs
 N6:ZZ
  the expected number of 6-secant line plus the number (-1) lines.
Description
  Text
    If there are only finitely many 6-secant lines then Le Barz' formula computes
    the sum of the number of 6-secants lines (with multiplicities) and the number of (-1)
    lines.
  Example
    kk=ZZ/nextPrime 10^4
    P4=kk[x_0..x_4]
    X=enriquesSurfaceOfDegree9 P4;
    d=degree X
    sg=sectionalGenus X
    xO=1+(genera X)_0
    N6=LeBarzN6(d,sg,xO)
    minimalBetti X
    K2=Ksquare(d,sg,xO)
    HK=HdotK(d,sg)
    d+2*HK+K2==10
    d+3*HK+2*K2==10
  Text
   Since the homogeneous ideal of this surface is generated by qunitics, there are no
   6-secant lines by Bezout. Thus, there is a (-1) line, which will be blown down by the first
   adjunction map. The image of the adjunction map defined by |H+K| is a
   surface X1 in P^{sg-1} of degree (H+K)^2=10, K1^2=K^2+1=0 and sectional
   genus sg1=6, since
   2sg1-2=(H+K).(H+2K)=10. It follows that X1 is a minimal Enriques surface.

   On the other hand the following surface has the same numerical invariants as the Enriques surface.
  Example
   X=nonspecialAlexanderSurface P4;
   d=degree X
   sg=sectionalGenus X
   xO=1+(genera X)_0
   minimalBetti X
  Text
   However, it has visibly a 6-secant line.
  Example
   L=residualInQuintics X
   dim L, degree L
   dim (X+L),degree (X+L)
References
   \textit{P. Le Barz}, Formules pour les multisecants des surfaces, C. R. Acad. Sci., Paris, Sér. I 292, 797- 800 (1981) Zbl 0492.14045) 
SeeAlso
   residualInQuintics
///

doc///
Key
 residualInQuintics
 (residualInQuintics,Ideal)
Headline
 compute the residual scheme to X in the ideal generated by the quintics
Usage
 Z = residualInQuintics X
Inputs
 X:Ideal
  homogenous ideal of a smooth projective surface in P4
Outputs
 Z:Ideal
  the residual ideal in the ideal generated by the quintics in X
Description
  Text
    If a surface in P4 has 6-secant lines,
    then any such line is contained in the vanishing locus of the residual ideal
    Z by Bezout. This allows us to compute the number of 6-secant lines
    and hence the number of (-1)-lines via Le 'Barz' 6-secant formula.
  CannedExample
    i1 : kk=ZZ/nextPrime 10^4

    o1 = kk

    o1 : QuotientRing
    i2 : P4=kk[x_0..x_4]

    o2 = P4

    o2 : PolynomialRing
    i3 : X=vBELSurface P4;

    o3 : Ideal of P4
    i4 : d=degree X

    o4 = 11
    i5 : sg=sectionalGenus X

    o5 = 11
    i6 : xO=1+(genera X)_0

    o6 = 1
    i7 : N6=LeBarzN6(d,sg,xO)

    o7 = 7
    i8 : minimalBetti X

                0 1  2 3 4
    o8 = total: 1 8 13 8 2
             0: 1 .  . . .
	     1: . .  . . .
	     2: . .  . . .
	     3: . 1  . . .
	     4: . 5  4 . .
	     5: . 2  9 8 2

    o8 : BettiTally
    i9 : Z=residualInQuintics X;

    o9 : Ideal of P4
    i10 : dim Z, degree Z

    o10 = (2, 2)

    o10 : Sequence
    i11 : tally apply(decompose Z,L->(dim L, degree L, degree (L+X)))

    o11 = Tally{(2, 1, 6) => 2}

    o11 : Tally
  Text
    Thus, there are two 6-secant lines and by Le Barz' 6-secant formula,
    the first adjunction map defined by |H+K| contracts five (-1)-lines.
  CannedExample
    i12 : K2=Ksquare(d,sg,xO)

    o12 = -11
    i13 : elapsedTime (numList,L2,L3,J)=adjunctionProcess(X,2);
    -- 16.3133s elapsed
    i14 : numList=={(4, 11, 11), 5, (10, 18, 9), 14, (8, 8, 1)}

    o14 = true
    i15 : degree J == 9-1

    o15 = true
    i16 : minimalBetti J

                 0  1  2  3  4  5 6
    o16 = total: 1 20 64 90 64 20 1
              0: 1  .  .  .  .  . .
	      1: . 20 64 90 64 20 .
	      2: .  .  .  .  .  . 1

    o16 : BettiTally
    i17 : sectionalGenus J==1

    o17 = true
    i18 : K2+5+14==9-1

    o18 = true

  Text
   Therefore, this surface arises as a blow-up of a Del Pezzo surface of degree 8
   in 14+5 points.
References
   \textit{P. Le Barz}, Formules pour les multisecants des surfaces, C. R. Acad. Sci., Paris, Sér. I 292, 797- 800 (1981) Zbl 0492.14045) 
SeeAlso
   LeBarzN6
   sectionalGenus
   Ksquare
///

-* for CannedExample selfIntersectionNumber

  Example
    kk=ZZ/nextPrime 10^4;
    P4=kk[x_0..x_4];
    X=K3surfaceD8 P4;
    pg=geometricGenus X
    d=degree X
    sg=sectionalGenus X
    xO=chiO(X)
    D=canonicalDivisor X;
    degree D==2
    genus D==0
    selfIntersectionNumber(X,D)==-1
    sectionalGenus X == 6
    Ksquare(d,sg,xO)
*-
doc///
Key
 canonicalDivisor
 (canonicalDivisor,Ideal)
Headline
 compute a canonical divisor on a surface with positive geometric genus
Usage
 D = canonicalDivisor X
Inputs
 X:Ideal
  homogenous ideal of a smooth projective surface in P4 
Outputs
 D:Ideal
  the ideal of an effective canonical divisor on X
Description
  Text
    If X is a smooth projective surface with pg>0, then X has an effective canonical
    divisor, which can be computed from the presentation matrix omegaX=Ext^1(X,P4^{-5}).
  CannedExample
    i1 : kk=ZZ/nextPrime 10^4;
    i2 : P4=kk[x_0..x_4];
    i3 : X=K3surfaceD8 P4;

    o3 : Ideal of P4
    i4 : pg=geometricGenus X

    o4 = 1
    i5 : d=degree X

    o5 = 8
    i6 : sg=sectionalGenus X

    o6 = 6
    i7 : xO=chiO(X)

    o7 = 2
    i8 : D=canonicalDivisor X;

    o8 : Ideal of P4
    i9 : degree D==2

    o9 = true
    i10 : genus D==0

    o10 = true
    i11 : selfIntersectionNumber(X,D)==-1

    o11 = true
    i12 : sectionalGenus X == 6

    o12 = true
    i13 : Ksquare(d,sg,xO)

    o13 = -1

  Text
    Thus, X is the projection from the tangent plane at a point p on a 
    minimal K3 surface X2 in P7 of degree 12=8+4. 
References
   \textit{Hartshorne, R.}, Algebraic Geometry , GTM 52, Springer (1977)
SeeAlso
   chiO
   sectionalGenus
   canonicalDivisor
   Ksquare
///
-* for CannedExample in selfIntersectionNumber

  Example
    kk=ZZ/nextPrime 10^4;
    P4=kk[x_0..x_4];
    X=K3surfaceD8 P4;
    pg=geometricGenus X
    d=degree X
    sg=sectionalGenus X
    xO=chiO(X)
    D=canonicalDivisor X;
    degree D==2
    genus D==0
    selfIntersectionNumber(X,D)==-1
    sectionalGenus X == 6
    Ksquare(d,sg,xO)

*-

doc///
Key
 selfIntersectionNumber
 (selfIntersectionNumber,Ideal,Ideal)
Headline
 compute the self-intersection number of an effective divisor on a smooth surface
Usage
 DdotD = selfIntersectionNumber(X,D)
Inputs
 X:Ideal
   homogenous ideal of a smooth projective surface
 D:Ideal
   homogeneous ideal of an effective divisor D on X 
Outputs
 DdotD:ZZ
    the self intersection number of D on X
Description
  Text
    The self-intersection number of an effective divisor can be computed from the genus g1 of D
    and the genus g2 of 2D, since
    
    2g1-2=D.(D+K) and 2g2-2 = 2D.(2D+K)

    hold.
  CannedExample
    i1 : kk=ZZ/nextPrime 10^4;
    i2 : P4=kk[x_0..x_4];
    i3 : X=K3surfaceD8 P4;

    o3 : Ideal of P4
    i4 : pg=geometricGenus X

    o4 = 1
    i5 : d=degree X

    o5 = 8
    i6 : sg=sectionalGenus X

    o6 = 6
    i7 : xO=chiO(X)

    o7 = 2
    i8 : D=canonicalDivisor X;

    o8 : Ideal of P4
    i9 : degree D==2

    o9 = true
    i10 : genus D==0

    o10 = true
    i11 : selfIntersectionNumber(X,D)==-1

    o11 = true
    i12 : sectionalGenus X == 6

    o12 = true
    i13 : Ksquare(d,sg,xO)

    o13 = -1
  Text
    Thus, X is the projection from the tangent plane at a point p of
    a minimal K3 surface X2 in P7 of degree 12=8+4. 
References
   \textit{Hartshorne, R.}, Algebraic Geometry , GTM 52, Springer (1977) (V.1.5)
SeeAlso
   chiO
   sectionalGenus
   canonicalDivisor
   Ksquare
///

-* for CannedExample in tateResolutionOfSurface

  Example
    kk=ZZ/nextPrime 10^4
    P4=kk[x_0..x_4]
    X=ellipticSurfaceD12S14Linfinite P4;
    minimalBetti X
    T=tateResolutionOfSurface X;
    "elapsedTime geometricGenus X == 2"; -- 52.2s elapsed
    betti T
    33==5*8-9+2
  Text
    For example, the entry 1 in homological degree -1 is $h^4(I_X(-5)) = h^4(O_{P4}(-5))=1$. 
    The entry 2 in homological degree 3 is $h^3(I_X)=h^2(O_X)=pg$.
    $h^0(I_X(6))=33=5*8-9+2$ which we can read off betti numbers of the minimal free
    resolution of X.

    Note that it might be faster to compute the geometric genus pg and the irregularity q of a surface
    by using the Tate resolution rather than sheaf cohomology.
    
    If the homogeneous ideal is generated by forms of degree <=6, then the truncation used in the computation
    can be choosen to be 6. If there are generatorsog higher degree, we might need a larger truncation.
  Example
    X=irregularEllipticSurfaceD12 P4;
    minimalBetti X
    betti tateResolutionOfSurface(X,7)
  Text
    The irregularity of this surface is q=1 and the geometric genus is pg=3.
    It is a minimal elliptic surface.
  Example
    sg=sectionalGenus X
    d=degree X
    xO=chiO(X)
    Ksquare(d,sg,xO)==0
    HdotK(d,sg)
    LeBarzN6(d,sg,xO)
    residual=residualInQuintics X;
    dim residual,degree residual
    primaryDecomposition residual;
    cH=primaryDecomposition saturate (X+ideal x_2);
    tally apply(cH,c->(dim c, degree c, degree radical c, minimalBetti c))
  Text
    Say something sensible.
*-

doc///
Key
 tateResolutionOfSurface
 (tateResolutionOfSurface,Ideal)
 (tateResolutionOfSurface,Ideal,ZZ)
Headline
 compute the Tate resolution of the ideal sheaf of a surface in P4
Usage
 T = tateResolutionOfSurface X
 T = tateResolutionOfSurface(X,n)
Inputs
 X:Ideal
  homogenous ideal of a smooth projective surface in P4
Outputs
 T: Complex
  the Tate resolution of the ideal sheaf of surface in P4
Description
  Text
    The Tate resolution T of a coherent sheaf F on a projective space P^n is an infinite
    exact complex of free modules over an exterior algebra E that encodes the cohomology groups of
    F:

    T^d(F) = sum_{i=0}^n Hom_kk(E,H^i(Pn,F(d-i))).

    For details see [EFS].
    In the case of a surface the interesting cohomology groups lie in the range d = -1..7.
    From the betti table of T we can read off the dimension of certain cohomology group.
  CannedExample
    i1 : kk=ZZ/nextPrime 10^4

    o1 = kk

    o1 : QuotientRing
    i2 : P4=kk[x_0..x_4]

    o2 = P4

    o2 : PolynomialRing
    i3 : X=ellipticSurfaceD12S14Linfinite P4;

    o3 : Ideal of P4
    i4 : minimalBetti X

                0  1  2 3 4
    o4 = total: 1 10 14 6 1
             0: 1  .  . . .
	     1: .  .  . . .
	     2: .  .  . . .
	     3: .  .  . . .
	     4: .  8  9 2 .
	     5: .  2  5 4 1

    o4 : BettiTally
    i5 : T=tateResolutionOfSurface X;
    i6 : "elapsedTime geometricGenus X == 2"; -- 52.2s elapsed
    i7 : betti T

                 -1  0  1  2 3 4 5  6  7
    o7 = total: 128 78 41 16 5 3 9 33 82
            -4:   1  .  .  . . . .  .  .
	    -3: 127 78 41 16 2 . .  .  .
	    -2:   .  .  .  . 3 2 .  .  .
	    -1:   .  .  .  . . 1 1  .  .
	     0:   .  .  .  . . . 8 33 82

    o7 : BettiTally
    i8 : 33==5*8-9+2

    o8 = true
  Text
    For example, the entry 1 in homological degree -1 is $h^4(I_X(-5)) = h^4(O_{P4}(-5))=1$.
    The entry 2 in homological degree 3 is $h^3(I_X)=h^2(O_X)=pg$. $h^0(I_X(6))=33=5*8-9+2$
    which we can read off betti numbers of the minimal free resolution of X.

    Note that it might be faster to compute the geometric genus pg and the irregularity q of
    a surface by using the Tate resolution rather than sheaf cohomology.

    If the homogeneous ideal is generated by forms of degree <=6, then the truncation used
    in the computation can be choosen to be 6. If there are generatorsog higher degree,
    we might need a larger truncation.
  CannedExample
    i9 : X=irregularEllipticSurfaceD12 P4;

    o9 : Ideal of P4
    i10 : minimalBetti X

                 0 1  2 3 4
    o10 = total: 1 9 15 9 2
              0: 1 .  . . .
	      1: . .  . . .
	      2: . .  . . .
	      3: . .  . . .
	      4: . 5  2 . .
	      5: . 4 10 4 .
	      6: . .  3 5 2

    o10 : BettiTally
    i11 : betti tateResolutionOfSurface(X,7)

                  -1  0  1  2 3 4  5  6  7   8
    o11 = total: 124 75 39 16 6 5 10 29 75 156
             -4:   1  .  .  . . .  .  .  .   .
	     -3: 123 75 39 15 3 .  .  .  .   .
	     -2:   .  .  .  1 2 1  .  .  .   .
	     -1:   .  .  .  . 1 4  5  2  .   .
	      0:   .  .  .  . . .  5 27 75 156

    o11 : BettiTally
  Text
    The irregularity of this surface is q=1 and the geometric genus is pg=3.
    It is a minimal elliptic surface.
  CannedExample
    i12 : sg=sectionalGenus X

    o12 = 13
    i13 : d=degree X

    o13 = 12
    i14 : xO=chiO(X)

    o14 = 3
    i15 : Ksquare(d,sg,xO)==0

    o15 = true
    i16 : HdotK(d,sg)

    o16 = 12
    i17 : LeBarzN6(d,sg,xO)

    o17 = 10
    i18 : residual=residualInQuintics X;

    o18 : Ideal of P4
    i19 : dim residual,degree residual

    o19 = (3, 3)

    o19 : Sequence
    i20 : primaryDecomposition residual;
    i21 : cH=primaryDecomposition saturate (X+ideal x_2);
    i22 : tally apply(cH,c->(dim c, degree c, degree radical c, minimalBetti c))

                                   0 1  2 3 4
    o22 = Tally{(2, 12, 12, total: 1 6 11 8 2) => 1}
                                0: 1 1  . . .
				1: . .  . . .
				2: . 1  1 . .
				3: . .  . . .
				4: . .  . . .
				5: . 4  7 3 .
				6: . .  3 5 2

    o22 : Tally
  Text
    Say something sensisible

References
   \textit{D. Eisenbud, G. Floystad, F.-O. Schreyer} Sheaf cohomology and free resolutions over exterior algebras, Trans. Am. Math. Soc. 355, No. 11, 4397-4426 (2003; Zbl 1063.14021)
SeeAlso
   geometricGenus
   irregularity
   chiO
///


-* for CannedExample in tangentToMonad
    
  Example
    kk=ZZ/19
    P4=kk[x_0..x_4]
    E=kk[e_0..e_4,SkewCommutative=>true]
    X=specificAboSurface(P4,E,1);
    minimalBetti X
    betti(T=tateResolutionOfSurface X)
    a=3, b=1, c=3, d=4
    m=tangentToMonad X;
    V=source m
    rank V - (a^2+b^2+5*b*c+c^2+d^2-1) == 36
  Text
    So the rank 2 reflexive sheaf E depends on at most 36 parameters and
    taking into acount h^0(E)=5
    we have an atmost 34+4=40 dimensional family of surfaces. 
    
    On the other hand X is the blowup of a polarized K3 surface in 6 points. So we
    get locqlly a family of dimension at least
  Example
    2*6+19-3*5+24==40
*-
doc///
Key
 tangentToMonad
 (tangentToMonad,Ideal)
Headline
 Compute the tangent space to the monad for a surface
Usage
  m = tangentToMonad X
Inputs
  X:Ideal
    homogenous ideal of a smooth projective surface in P4
Outputs
  m:Matrix
   which describes the first order deformation space for the monad of X
Description
  Text
    This command computes the dimension of the tangent space to the space 'V' of monads
    of the form 'M' a*Omega^3(3)->b*Omega^2(2)++c*Omega^1(1)->d*OO at a specfic example
    by taking the derivative of the composite of differentials 'alpha' and 'beta'.
    The dimension of the space of isomophism classes of monads is at most
    dim V-(a^2+b^2+c^2+5*b*c+d^2-1).
    In the example below we have a=3, b=1, c=3, d=4
  CannedExample
    i1 : kk=ZZ/19

    o1 = kk

    o1 : QuotientRing
    i2 : P4=kk[x_0..x_4]

    o2 = P4

    o2 : PolynomialRing
    i3 : E=kk[e_0..e_4,SkewCommutative=>true]

    o3 = E

    o3 : PolynomialRing, 5 skew commutative variable(s)
    i4 : X=specificAboSurface(P4,E,1);

    o4 : Ideal of P4
    i5 : minimalBetti X

                0  1  2  3 4
    o5 = total: 1 12 24 17 4
             0: 1  .  .  . .
	     1: .  .  .  . .
	     2: .  .  .  . .
	     3: .  .  .  . .
	     4: .  4  .  . .
	     5: .  8 24 17 4

    o5 : BettiTally
    i6 : betti(T=tateResolutionOfSurface X)

                 -1  0  1  2 3 4 5  6  7
    o6 = total: 123 74 38 14 4 4 8 28 76
            -4:   1  .  .  . . . .  .  .
	    -3: 122 74 38 14 1 . .  .  .
	    -2:   .  .  .  . 3 1 .  .  .
	    -1:   .  .  .  . . 3 4  .  .
	     0:   .  .  .  . . . 4 28 76

    o6 : BettiTally
    i7 : a=3, b=1, c=3, d=4

    o7 = (3, 1, 3, 4)

    o7 : Sequence
    i8 : m=tangentToMonad X;

                           28                 85
    o8 : Matrix (kk[e ..e ])   <-- (kk[e ..e ])
                     0   4              0   4
    i9 : V=source m

                    85
    o9 = (kk[e ..e ])
             0   4

    o9 : kk[e ..e ]-module, free, degrees {85:6}
             0   4
    i10 : rank V - (a^2+b^2+5*b*c+c^2+d^2-1) == 36

    o10 = true
  Text
    So the rank 2 reflexive sheaf E depends on at most 36 parameters
    and taking into acount h^0(E)=5 we have an atmost 34+4=40 dimensional family of surfaces.
    On the other hand X is the blowup of a polarized K3 surface in 6 points. So we get locally
    a family of dimension at least
  CannedExample
    i11 : 2*6+19-3*5+24==40

    o11 = true
  Text
    Thus the space of monads for the ideal sheaf is smooth of the expected dimension 40
    at the given point. 
    A transversal slice defined over ZZ to the space of monads through the given point
    over ZZ/19 defines
    an number field K, a prime with residue field ZZ/19 and a smooth family of surface over an open
    part of Spec O_K, which specializes to the given surface.
    The fiber over the generic point of
    Spec O_K is a lifting to characteristic 0.
///




-* schreyer surfaces *-

-* for cannedExample in moduleFromSchreyerSurface
  Example
    P4=ZZ/3[x_0..x_4];
    (Ms,Types)=exampleOfSchreyerSurfaces P4;
    tally apply(Ms,M->minimalBetti M)
    X=schreyerSurfaceFromModule Ms_1;
    minimalBetti X
    M=moduleFromSchreyerSurface X;
    minimalBetti M
*-
doc///
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
    with Hilbert function (1,5,5) and at least two extra syzygies.
  CannedExample
    i1 : P4=ZZ/3[x_0..x_4];
    i2 : (Ms,Types)=exampleOfSchreyerSurfaces P4;
    i3 : tally apply(Ms,M->minimalBetti M)

                      0  1  2  3  4 5
    o3 = Tally{total: 1 10 22 28 20 5 => 4}
                   0: 1  .  .  .  . .
		   1: . 10 15  2  . .
		   2: .  .  7 26 20 5
                      0  1  2  3  4 5
               total: 1 10 23 29 20 5 => 3
                   0: 1  .  .  .  . .
		   1: . 10 15  3  . .
		   2: .  .  8 26 20 5
                      0  1  2  3  4 5
               total: 1 10 24 30 20 5 => 1
                   0: 1  .  .  .  . .
		   1: . 10 15  4  . .
		   2: .  .  9 26 20 5
                      0  1  2  3  4 5
               total: 1 10 25 31 20 5 => 1
                   0: 1  .  .  .  . .
		   1: . 10 15  5  . .
		   2: .  . 10 26 20 5

    o3 : Tally
    i4 : X=schreyerSurfaceFromModule Ms_1;

    o4 : Ideal of P4
    i5 : minimalBetti X

                0  1  2  3 4
    o5 = total: 1 12 26 20 5
             0: 1  .  .  . .
	     1: .  .  .  . .
	     2: .  .  .  . .
	     3: .  .  .  . .
	     4: .  5  .  . .
	     5: .  7 26 20 5

    o5 : BettiTally
    i6 : M=moduleFromSchreyerSurface X;

    o6 : Ideal of P4
    i7 : minimalBetti M

                0  1  2  3  4 5
    o7 = total: 1 10 22 28 20 5
             0: 1  .  .  .  . .
	     1: . 10 15  2  . .
	     2: .  .  7 26 20 5

    o7 : BettiTally
  
///

-* for CannedExample in schreyerSurfaceFromModule
  Example
    P4=ZZ/3[x_0..x_4];
    (Ms,Types)=exampleOfSchreyerSurfaces P4;
    tally apply(Ms,M->minimalBetti M)
    X=schreyerSurfaceFromModule Ms_1;
    minimalBetti X
    M=moduleFromSchreyerSurface X;
    minimalBetti M
*-

doc///
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
    with Hilbert function (1,5,5) and at least two extra syzygies.
  CannedExample
     i1 : P4=ZZ/3[x_0..x_4];
     i2 : (Ms,Types)=exampleOfSchreyerSurfaces P4;
     i3 : tally apply(Ms,M->minimalBetti M)

                       0  1  2  3  4 5
     o3 = Tally{total: 1 10 22 28 20 5 => 4}
                    0: 1  .  .  .  . .
		    1: . 10 15  2  . .
		    2: .  .  7 26 20 5
                       0  1  2  3  4 5
                total: 1 10 23 29 20 5 => 3
                    0: 1  .  .  .  . .
		    1: . 10 15  3  . .
		    2: .  .  8 26 20 5
                      0  1  2  3  4 5
                total: 1 10 24 30 20 5 => 1
                    0: 1  .  .  .  . .
		    1: . 10 15  4  . .
		    2: .  .  9 26 20 5
                      0  1  2  3  4 5
                total: 1 10 25 31 20 5 => 1
		    0: 1  .  .  .  . .
		    1: . 10 15  5  . .
		    2: .  . 10 26 20 5

     o3 : Tally
     i4 : X=schreyerSurfaceFromModule Ms_1;

     o4 : Ideal of P4
     i5 : minimalBetti X

                 0  1  2  3 4
     o5 = total: 1 12 26 20 5
              0: 1  .  .  . .
	      1: .  .  .  . .
	      2: .  .  .  . .
	      3: .  .  .  . .
	      4: .  5  .  . .
	      5: .  7 26 20 5

     o5 : BettiTally
     i6 : M=moduleFromSchreyerSurface X;

     o6 : Ideal of P4
     i7 : minimalBetti M

                 0  1  2  3  4 5
     o7 = total: 1 10 22 28 20 5
              0: 1  .  .  .  . .
              1: . 10 15  2  . .
              2: .  .  7 26 20 5

     o7 : BettiTally


References
   \textit{Schreyer, F.-O.}, Small fields in constructive algebraic geometry, in Moduli of Vector bundles, Sanda 1994, Lecture Notes in Pure and Appl. Math., 179, (1996), 221-228 

///

-* for CannedExample schreyerSurfaceWith2LinearSyzygies
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
    at two (common) points.     
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
*-



doc///
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
    The construction uses a 2-step liaison.
    The desired surface has a residual scheme R=X5:X consisting of the union of 3 planes.
    A general (5,5) complete intersection ci has as residual scheme ci:X=R cup Y with
    Y a surface of degree 11 which lies on two quartics. The (4,4) complete intersection
    ci2 has residual Z=ci2:Y of degree 5 which decomposes in a cubic scroll and a quadric surface
    which intersect along the directrix of the scroll and two non-CM points of Z.
  CannedExample
    i1 : kk=ZZ/nextPrime(2*10^3);P4=kk[x_0..x_4];
    i3 : X=schreyerSurfaceWith2LinearSyzygies(P4);
    dim singX=-1

    o3 : Ideal of P4
    i4 : elapsedTime X=schreyerSurfaceWith2LinearSyzygies(P4);
    dim singX=-1
    -- 11.4269s elapsed

    o4 : Ideal of P4
    i5 : minimalBetti X

                0  1  2  3 4
    o5 = total: 1 14 28 20 5
             0: 1  .  .  . .
	     1: .  .  .  . .
	     2: .  .  .  . .
	     3: .  .  .  . .
	     4: .  5  2  . .
	     5: .  9 26 20 5

    o5 : BettiTally
    i6 : M=moduleFromSchreyerSurface X;

    o6 : Ideal of P4
    i7 : minimalBetti M

                0  1  2  3  4 5
    o7 = total: 1 10 24 30 20 5
             0: 1  .  .  .  . .
	     1: . 10 15  4  . .
	     2: .  .  9 26 20 5

    o7 : BettiTally
    i8 : X5=ideal (gens X)_{0..4};

    o8 : Ideal of P4
    i9 : R=X5:X;

    o9 : Ideal of P4
    i10 : minimalBetti radical R

                 0 1 2
    o10 = total: 1 3 2
              0: 1 . .
              1: . 3 2

    o10 : BettiTally
    i11 : tally apply(decompose R,c->(dim c, degree c, minimalBetti c))

                              0 1 2
    o11 = Tally{(3, 1, total: 1 2 1) => 3}
                           0: 1 2 1

    o11 : Tally
    i12 : ci=ideal( gens X*random(source gens X,P4^{2:-5}));

    o12 : Ideal of P4
    i13 : Y=(ci:X):R;

    o13 : Ideal of P4
    i14 : degree Y,betti(fY=res Y)

                        0 1 2 3
    o14 = (11, total: 1 6 7 2)
                   0: 1 . . .
		   1: . . . .
		   2: . . . .
		   3: . 2 . .
		   4: . 4 7 2

    o14 : Sequence
    i15 : nCM=decompose ann coker transpose fY.dd_3

    o15 = {ideal (x , x , x , x  + 896x ), ideal (x , x  - 797x , x , x )}
                   4   2   1   0       3           3   2       4   1   0

    o15 : List
    i16 : ci2=ideal (gens Y)_{0,1};

    o16 : Ideal of P4
    i17 : Z=ci2:Y;

    o17 : Ideal of P4
    i18 : minimalBetti Z

    0 1  2 3 4
    o18 = total: 1 7 10 5 1
    0: 1 .  . . .
    1: . .  . . .
    2: . 3  2 . .
    3: . 4  8 5 1

    o18 : BettiTally
    i19 : cZ=decompose Z;
    i20 : tally apply(cZ,c->(dim c, degree c, minimalBetti c))

                              0 1 2
    o20 = Tally{(3, 2, total: 1 2 1) => 1}
                           0: 1 1 .
                           1: . 1 1
                              0 1 2
                (3, 3, total: 1 3 2) => 1
                           0: 1 . .
			   1: . 3 2

    o20 : Tally
  Text
    The construction is a reversal of this linkage. Note that both Y and Z are not
    Cohen-Macaulay at two (common) points.
  CannedExample
    i21 : intersectionOftheTwoComponentsOfZ=sum(cZ);

    o21 : Ideal of P4
    i22 : apply(cI=decompose intersectionOftheTwoComponentsOfZ,c->(dim c, degree c))

    o22 = {(2, 1), (1, 1), (1, 1)}

    o22 : List
    i23 : cI, cI_{1,2}==nCM

    o23 = ({ideal (x  - 165x , x , x  + 168x ), ideal (x , x , x , x  + 896x ),
	            2       4   1   0       3           4   2   1   0       3  
         -----------------------------------------------------------------------
	    ideal (x , x  - 797x , x , x )}, true)
                    3   2       4   1   0

    o23 : Sequence
    i24 : planes=decompose R

    o24 = {ideal (x  - 186x  + 20x , x  - 538x  + 144x ), ideal (x  - 275x  +
	           1       2      4   0       2       4           1       2  
	    -----------------------------------------------------------------------
	    716x  - 52x , x  - 652x  + 422x  + 952x ), ideal (x  - 570x , x  -
	        3      4   0       2       3       4           1       2   0  
	    -----------------------------------------------------------------------
	    798x  + 896x )}
                2       3

    o24 : List
    i25 : matrix apply(planes,p2->apply(nCM,p->dim(p2+p)))

    o25 = | 0 1 |
          | 0 0 |
          | 1 0 |

                   3       2
    o25 : Matrix ZZ  <-- ZZ
    i26 : matrix apply(planes,p2->apply(planes,p2'->dim(p2+p2')))

    o26 = | 3 2 1 |
          | 2 3 2 |
          | 1 2 3 |

                   3       3
    o26 : Matrix ZZ  <-- ZZ
    i27 : dim(radical R+Z),degree(radical R+Z)

    o27 = (1, 17)

    o27 : Sequence
    i28 : matrix apply(planes,p2->apply(cZ,c->degree(p2+c)))

    o28 = | 2 3 |
          | 2 3 |
          | 2 3 |

                   3       2
    o28 : Matrix ZZ  <-- ZZ
    i29 : m3x2=(res cZ_1).dd_2

    o29 = {2} | -x_1+433x_2+549x_3-879x_4 -x_2-826x_4    |
          {2} | x_0+332x_2-603x_3+974x_4  -579x_2-673x_4 |
          {2} | 620x_3-23x_4              x_1+384x_4     |

                   3       2
    o29 : Matrix P4  <-- P4
    i30 : syz transpose (m3x2%cI_0) -- => cI_0 is the directrix of the scroll

    o30 = {-2} | 483 -895 |
          {-2} | 1   0    |
          {-2} | 0   1    |

                   3       2
    o30 : Matrix P4  <-- P4
  
///


-* for cannedExample schreyerSurfaceWith2or3LinearSyzygies
  Example
    kk=ZZ/nextPrime(2*10^3);P4=kk[x_0..x_4];
    elapsedTime X=schreyerSurfaceWith2or3LinearSyzygies(P4,2);
    minimalBetti X
    M=moduleFromSchreyerSurface X;
    minimalBetti M
    R=residualInQuintics X;
    tally apply(primaryDecomposition R,c->(dim c, degree c, minimalBetti c))
    ci=ideal( gens X*random(source gens X,P4^{2:-5}));
    Y=(ci:X):R;
    degree (ci:X)
    degree Y,betti(fY=res Y)
    nCM=decompose ann coker transpose fY.dd_3
    ci2=ideal (gens Y)_{0,1};
    Z=ci2:Y;
    minimalBetti Z
    cZ=decompose Z;
    tally apply(cZ,c->(dim c, degree c, minimalBetti c))
  Text
    The construction is a reversal of this linkage. Note that both Y and Z are not Cohen-Macaulay
    at two (common) points.     
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
    cI_0
    syz transpose (m3x2%cI_0) -- => cI_0 is the directrix of the scroll
  Text
    In case s=3, the residual scheme to the surface in the quintics consists of 5 planes.
  Example
    elapsedTime X=schreyerSurfaceWith2or3LinearSyzygies(P4,3);
    minimalBetti X
    M=moduleFromSchreyerSurface X;
    minimalBetti M
    R=residualInQuintics X;
    cR=decompose R;
    tally apply(cR,c->(dim c, degree c))
    ci=ideal( gens X*random(source gens X,P4^{2:-5}));
    Y=(ci:X):R;
    degree (ci:X)
    degree Y,betti(fY=res Y), sectionalGenus Y
    apply(cR,p->dim trim(p+Y))
    matrix apply(cR|{Y},p->apply(cR|{Y},q-> dim(p+q)))
    betti tateResolutionOfSurface Y
    betti tateResolutionOfSurface X
    Ksquare(9,9,4)
    HdotK(9,9)
    K=canonicalDivisor Y;
    degree Y, degree K
    saturate ideal singularLocus Y
    selfIntersectionNumber(Y,K)
*-

doc///
Key
 schreyerSurfaceWith2or3LinearSyzygies
 (schreyerSurfaceWith2or3LinearSyzygies, Ring, ZZ)
 [schreyerSurfaceWith2or3LinearSyzygies,Smooth]
Headline
 compute a rational Schreyer surface whose H^1-module has 4 or 5 extra syzyzgies
Usage
 X = schreyerSurfaceWith2or3LinearSyzygies(P4,s)
Inputs
 P4:Ring
  the coordinate ring of P4
 s: ZZ
   a number s=2 or s=3
Outputs
 X:Ideal
  the ideal of a smooth Schreyer surface
Description
  Text
    The construction uses a 2-step liaison.
    In case of s=2, the desired surface has a residual scheme R=X5:X consisting of the union of 3 planes.
    A general (5,5) complete intersection ci has as residual scheme ci:X=R cup Y with
    Y a surface of degree 11 which lies on two quartics. The (4,4) complete intersection
    ci2 has residual Z=ci2:Y of degree 5 which decomposes in a cubic scroll and a quadric surface
    which intersect along the directrix of the scroll and two non-CM points of Z.
  CannedExample
    i1 : kk=ZZ/nextPrime(2*10^3);P4=kk[x_0..x_4];
    i3 : elapsedTime X=schreyerSurfaceWith2or3LinearSyzygies(P4,2);
      dim singX=-1
    -- 11.0011s elapsed

    o3 : Ideal of P4
    i4 : minimalBetti X

                0  1  2  3 4
    o4 = total: 1 14 28 20 5
             0: 1  .  .  . .
             1: .  .  .  . .
             2: .  .  .  . .
	     3: .  .  .  . .
	     4: .  5  2  . .
	     5: .  9 26 20 5

    o4 : BettiTally
    i5 : M=moduleFromSchreyerSurface X;

    o5 : Ideal of P4
    i6 : minimalBetti M

                0  1  2  3  4 5
    o6 = total: 1 10 24 30 20 5
             0: 1  .  .  .  . .
	     1: . 10 15  4  . .
	     2: .  .  9 26 20 5

    o6 : BettiTally
    i7 : R=residualInQuintics X;

    o7 : Ideal of P4
    i8 : tally apply(primaryDecomposition R,c->(dim c, degree c, minimalBetti c))

                             0 1 2
    o8 = Tally{(3, 1, total: 1 2 1) => 3    }
                          0: 1 2 1
                            0 1 2 3 4
              (2, 2, total: 1 5 8 5 1) => 2
                         0: 1 1 . . .
                         1: . 4 8 5 1

    o8 : Tally
    i9 : ci=ideal( gens X*random(source gens X,P4^{2:-5}));

    o9 : Ideal of P4
    i10 : Y=(ci:X):R;

    o10 : Ideal of P4
    i11 : degree (ci:X)

    o11 = 14
    i12 : degree Y,betti(fY=res Y)

                      0 1 2 3
    o12 = (11, total: 1 6 7 2)
                   0: 1 . . .
                   1: . . . .
		   2: . . . .
		   3: . 2 . .
		   4: . 4 7 2

    o12 : Sequence
    i13 : nCM=decompose ann coker transpose fY.dd_3

    o13 = {ideal (x , x , x , x  - 998x ), ideal (x , x  - 739x , x , x )}
                   4   2   1   0       3           3   2       4   1   0

    o13 : List
    i14 : ci2=ideal (gens Y)_{0,1};

    o14 : Ideal of P4
    i15 : Z=ci2:Y;

    o15 : Ideal of P4
    i16 : minimalBetti Z

                 0 1  2 3 4
    o16 = total: 1 7 10 5 1
             0: 1 .  . . .
	     1: . .  . . .
	     2: . 3  2 . .
	     3: . 4  8 5 1

    o16 : BettiTally
    i17 : cZ=decompose Z;
    i18 : tally apply(cZ,c->(dim c, degree c, minimalBetti c))

                              0 1 2
    o18 = Tally{(3, 2, total: 1 2 1) => 1}
                           0: 1 1 .
                           1: . 1 1
                              0 1 2
                (3, 3, total: 1 3 2) => 1
                           0: 1 . .
			   1: . 3 2

    o18 : Tally
  Text
    The construction is a reversal of this linkage. Note that both Y and Z are not Cohen-Macaulay
    at two (common) points.   
  CannedExample
    i19 : intersectionOftheTwoComponentsOfZ=sum(cZ);

    o19 : Ideal of P4
    i20 : apply(cI=decompose intersectionOftheTwoComponentsOfZ,c->(dim c, degree c))

    o20 = {(2, 1), (1, 1), (1, 1)}

    o20 : List
    i21 : cI, cI_{1,2}==nCM

    o21 = ({ideal (x  - 708x , x , x  + 138x ), ideal (x , x , x , x  - 998x ),
	            2       4   1   0       3           4   2   1   0       3  
	    -----------------------------------------------------------------------
	    ideal (x , x  - 739x , x , x )}, true)
                    3   2       4   1   0

    o21 : Sequence
    i22 : planes=decompose R

    o22 = {ideal (x  - 824x  - 722x  + 678x , x  + 600x  - 180x  + 508x ), ideal
              	   1       2       3       4   0       2       3       4        
	-----------------------------------------------------------------------
	(x  + 814x , x  + 37x  - 998x ), ideal (x  + 130x  + 74x , x  + 799x  +
	  1       2   0      2       3           1       2      4   0       2  
	    -----------------------------------------------------------------------
	    424x )}
                4

    o22 : List
    i23 : matrix apply(planes,p2->apply(nCM,p->dim(p2+p)))

    o23 = | 0 0 |
          | 1 0 |
          | 0 1 |

                   3       2
    o23 : Matrix ZZ  <-- ZZ
    i24 : matrix apply(planes,p2->apply(planes,p2'->dim(p2+p2')))

    o24 = | 3 2 2 |
          | 2 3 1 |
          | 2 1 3 |

                   3       3
    o24 : Matrix ZZ  <-- ZZ
    i25 : dim(radical R+Z),degree(radical R+Z)

    o25 = (1, 17)

    o25 : Sequence
    i26 : matrix apply(planes,p2->apply(cZ,c->degree(p2+c)))

    o26 = | 2 3 |
          | 2 3 |
          | 2 3 |

                   3       2
    o26 : Matrix ZZ  <-- ZZ
    i27 : m3x2=(res cZ_1).dd_2

    o27 = {2} | -x_1-567x_2-601x_3+230x_4 -x_2-639x_4 |
          {2} | x_0-302x_2-885x_3-600x_4  3x_2+709x_4 |
          {2} | -994x_3-619x_4            x_1+875x_4  |

                   3       2
    o27 : Matrix P4  <-- P4
    i28 : cI_0

    o28 = ideal (x  - 708x , x , x  + 138x )
                  2       4   1   0       3

    o28 : Ideal of P4
    i29 : syz transpose (m3x2%cI_0) -- => cI_0 is the directrix of the scroll

    o29 = {-2} | -215 75 |
          {-2} | 1    0  |
          {-2} | 0    1  |

                   3       2
    o29 : Matrix P4  <-- P4
  Text
    In case s=3, the residual scheme to the surface in the quintics consists of 5 planes.
  CannedExample
    i30 : elapsedTime X=schreyerSurfaceWith2or3LinearSyzygies(P4,3);
      dim singX=-1
    -- 11.1736s elapsed

    o30 : Ideal of P4
    i31 : minimalBetti X

                 0  1  2  3 4
    o31 = total: 1 15 29 20 5
              0: 1  .  .  . .
	      1: .  .  .  . .
	      2: .  .  .  . .
	      3: .  .  .  . .
	      4: .  5  3  . .
	      5: . 10 26 20 5

    o31 : BettiTally
    i32 : M=moduleFromSchreyerSurface X;

    o32 : Ideal of P4
    i33 : minimalBetti M

                 0  1  2  3  4 5
    o33 = total: 1 10 25 31 20 5
              0: 1  .  .  .  . .
	      1: . 10 15  5  . .
	      2: .  . 10 26 20 5

    o33 : BettiTally
    i34 : R=residualInQuintics X;

    o34 : Ideal of P4
    i35 : cR=decompose R;
    i36 : tally apply(cR,c->(dim c, degree c))

    o36 = Tally{(3, 1) => 5}

    o36 : Tally
    i37 : ci=ideal( gens X*random(source gens X,P4^{2:-5}));

    o37 : Ideal of P4
    i38 : Y=(ci:X):R;

    o38 : Ideal of P4
    i39 : degree (ci:X)

    o39 = 14
    i40 : degree Y,betti(fY=res Y), sectionalGenus Y

                     0 1 2
    o40 = (9, total: 1 4 3, 9)
                  0: 1 . .
		  1: . . .
		  2: . 1 .
		  3: . 3 3

    o40 : Sequence
    i41 : apply(cR,p->dim trim(p+Y))

    o41 = {2, 2, 2, 2, 2}

    o41 : List
    i42 : matrix apply(cR|{Y},p->apply(cR|{Y},q-> dim(p+q)))

    o42 = | 3 2 1 1 2 2 |
          | 2 3 1 2 1 2 |
          | 1 1 3 2 2 2 |
          | 1 2 2 3 1 2 |
          | 2 1 2 1 3 2 |
          | 2 2 2 2 2 3 |

                   6       6
    o42 : Matrix ZZ  <-- ZZ
    i43 : betti tateResolutionOfSurface Y

                 -1  0  1  2 3 4  5  6   7
    o43 = total: 91 55 29 12 4 8 27 65 130
             -4:  1  .  .  . . .  .  .   .
	     -3: 90 55 29 12 3 .  .  .   .
	     -2:  .  .  .  . . .  .  .   .
	     -1:  .  .  .  . . .  .  .   .
	      0:  .  .  .  . 1 8 27 65 130

    o43 : BettiTally
    i44 : betti tateResolutionOfSurface X

                  -1  0  1  2 3 4  5  6  7
    o44 = total: 104 61 30 10 3 5 10 32 84
             -4:   1  .  .  . . .  .  .  .
	     -3: 103 61 30 10 . .  .  .  .
	     -2:   .  .  .  . 2 .  .  .  .
	     -1:   .  .  .  . 1 5  5  .  .
	      0:   .  .  .  . . .  5 32 84

    o44 : BettiTally
    i45 : Ksquare(9,9,4)

    o45 = 2
    i46 : HdotK(9,9)

    o46 = 7
    i47 : K=canonicalDivisor Y;

    o47 : Ideal of P4
    i48 : degree Y, degree K

    o48 = (9, 7)

    o48 : Sequence
    i49 : saturate ideal singularLocus Y

    o49 = ideal 1

    o49 : Ideal of P4
    i50 : selfIntersectionNumber(Y,K)

    o50 = 2

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

-* for CannedExample unirationalConstructionOfSchreyerSurface
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
*-

doc///
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
  CannedExample  
    i1 : kk=ZZ/nextPrime 10^3;
    i2 : P4=kk[x_0..x_4];
    i3 : X=unirationalConstructionOfSchreyerSurface(P4);

    o3 : Ideal of P4
    i4 : minimalBetti X

                0  1  2  3 4
    o4 = total: 1 15 29 20 5
             0: 1  .  .  . .
	     1: .  .  .  . .
	     2: .  .  .  . .
	     3: .  .  .  . .
	     4: .  5  3  . .
	     5: . 10 26 20 5

    o4 : BettiTally
    i5 : M=moduleFromSchreyerSurface X;

    o5 : Ideal of P4
    i6 : minimalBetti M

                0  1  2  3  4 5
    o6 = total: 1 10 25 31 20 5
             0: 1  .  .  .  . .
             1: . 10 15  5  . .
             2: .  . 10 26 20 5

    o6 : BettiTally
    i7 : X5=ideal (gens X)_{0..4};

    o7 : Ideal of P4
    i8 : R=X5:X;

    o8 : Ideal of P4
    i9 : minimalBetti R

                0 1 2 3
    o9 = total: 1 5 5 1
             0: 1 . . .
	     1: . . . .
	     2: . 5 5 1

    o9 : BettiTally
    i10 : planes=decompose R

    o10 = {ideal (x , x ), ideal (x , x ), ideal (x , x ), ideal (x , x ), ideal
                   1   0           2   1           3   2           4   0        
	-----------------------------------------------------------------------
	(x , x )}
          4   3

    o10 : List
    i11 : tangentDimension M

    o11 = 30
    i12 : tally apply(planes,p->tally apply(decompose(p+X),c->(dim c, degree c, betti c)))

                                    0 1
    o12 = Tally{Tally{(1, 1, total: 1 4) => 3} => 5}
                                 0: 1 4
                  0 1
    (2, 4, total: 1 3) => 1
               0: 1 2
	       1: . .
	       2: . .
	       3: . 1

    o12 : Tally
    i13 : sixSecants1=apply(planes,p-> ideal (gens intersect drop(select(decompose(p+X),c->dim c==1),1))_{0,1,2});
    i14 : sixSecants2=apply(5,i->trim (planes_i+planes_((i+1)%5)));
    i15 : sixSecants=sixSecants1|sixSecants2

    o15 = {ideal (x  - 294x  + 146x , x , x ), ideal (x , x , x  - 145x  +
	           2       3       4   1   0           2   1   0       3  
	    -----------------------------------------------------------------------
	    288x ), ideal (x , x , x  - 267x  - 266x ), ideal (x , x  + 276x  -
	        4           3   2   0       1       4           4   1       2  
	    -----------------------------------------------------------------------
	    295x , x ), ideal (x , x , x  + 127x  - 209x ), ideal (x , x , x ),
        	3   0           4   3   0       1       2           2   1   0  
	-----------------------------------------------------------------------
	ideal (x , x , x ), ideal (x , x , x , x ), ideal (x , x , x ), ideal
        	3   2   1           4   3   2   0           4   3   0        
	-----------------------------------------------------------------------
	(x , x , x , x )}
          4   3   1   0

    o15 : List
    i16 : tally apply(sixSecants, l-> (betti l,dim l, degree (l+X)))

                        0 1
    o16 = Tally{(total: 1 3, 2, 6) => 8}
                     0: 1 3
            0 1
    (total: 1 4, 1, 1) => 2
         0: 1 4

    o16 : Tally
    i17 : LeBarzN6(11,10,1)==10

    o17 = true
    

  Text
    Each of the five planes intersects X in a plane quartic curve and three points.
    The 6-secants are the five intersection lines of the planes and the five lines spanned by two of
    the special points in each plane.
///
 -* for CannedExample specialEnriquesSchreyerSurface
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
*-

doc///
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
    The desired surface has a residual scheme R=X5:X, which is a quintic elliptic scroll.
    The H^1-module is defined as the sum of the ideals of two elliptic curves on the scroll.
    Thus, the construction needs a point p on the Bring curve and two points on the conic of
    elliptic normal curves of degree 5. Over a finite field such data are easily found by a random search, whose running time
    is independent of the finite ground field
    The two points on the conic are the intersection of the conic with the polar line to the point p of the conic, [Hulek,199x].
    The rest of the construction is unirational.
  CannedExample
    i1 : kk=ZZ/nextPrime 10^3;
    i2 : P4=kk[x_0..x_4];
    i3 : X=specialEnriquesSchreyerSurface(P4);

    o3 : Ideal of P4
    i4 : minimalBetti X

                0  1  2  3 4
    o4 = total: 1 15 29 20 5
             0: 1  .  .  . .
	     1: .  .  .  . .
	     2: .  .  .  . .
	     3: .  .  .  . .
	     4: .  5  3  . .
	     5: . 10 26 20 5

    o4 : BettiTally
    i5 : M=moduleFromSchreyerSurface X;

    o5 : Ideal of P4
    i6 : minimalBetti M

                0  1  2  3  4 5
    o6 = total: 1 10 25 31 20 5
             0: 1  .  .  .  . .
	     1: . 10 15  5  . .
	     2: .  . 10 26 20 5

    o6 : BettiTally
    i7 : X5=ideal (gens X)_{0..4};

    o7 : Ideal of P4
    i8 : R=X5:X;

    o8 : Ideal of P4
    i9 : minimalBetti R

                0 1 2 3
    o9 = total: 1 5 5 1
             0: 1 . . .
	     1: . . . .
	     2: . 5 5 1

    o9 : BettiTally
    i10 : tangentDimension M==25

    o10 = true
  Text
    => These surfaces do not form a complete family, i.e., this family is part of a
    family of larger dimension.
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
-* for CannedExample specificSchreyerSurface
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
    There are 6 six-secant lines grouped into Frobenius orbits.
    So there should be 4 (-1) lines. Indeed, the adjunction data confirm this.
    The last surface in the adjunction process is a conic bundle with
    6+8-5=9 singular fibers.

    The construction of X uses a special Hartshorne-Rao module M.   
  Example
    betti tateResolutionOfSurface X
    M=moduleFromSchreyerSurface X;
    minimalBetti M
    tangentDimension M==36

*-


doc///
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
    The function returns one of ten specific smooth Schreyer surfaces.
    It prints the corresponding adjunction process data.
    The corresponding H^1-module is precomputed and stored in the function exampleOfSchreyerSurfaces.
  CannedExample
    i1 : P4=ZZ/3[x_0..x_4];
    i2 : X=specificSchreyerSurface(P4,1);
    {(4, 11, 10), 4, (9, 19, 11), 1, (10, 19, 10), 0, (9, 16, 8), 0, (7, 11, 5), 5, (4, 4, 1)}

    o2 : Ideal of P4
    i3 : (d,sg)=(degree X, sectionalGenus X)

    o3 = (11, 10)

    o3 : Sequence
    i4 : Ksquare(d,sg,1)==-6

    o4 = true
    i5 : LeBarzN6(d,sg,1)==10

    o5 = true
    i6 : minimalBetti X

                0  1  2  3 4
    o6 = total: 1 12 26 20 5
             0: 1  .  .  . .
	     1: .  .  .  . .
	     2: .  .  .  . .
	     3: .  .  .  . .
	     4: .  5  .  . .
	     5: .  7 26 20 5

    o6 : BettiTally
    i7 : betti(X5=ideal (gens X)_{0..4})

                0 1
    o7 = total: 1 5
             0: 1 .
	     1: . .
	     2: . .
	     3: . .
	     4: . 5

    o7 : BettiTally
    i8 : betti(residual=X5:X)

                0  1
    o8 = total: 1 11
             0: 1  .
	     1: .  .
	     2: . 11

    o8 : BettiTally
    i9 : dim residual,degree residual

    o9 = (2, 6)

    o9 : Sequence
    i10 : tally apply(primaryDecomposition residual,c-> (
	    (dim c, degree c, degree (c+X))))

    o10 = Tally{(2, 2, 12) => 3}

    o10 : Tally
  Text
    There are 6 six-secant lines grouped into Frobenius orbits.
    So there should be 4 (-1) lines. Indeed, the adjunction data confirm this.
    The last surface in the adjunction process is a conic bundle with 6+8-5=9 singular fibers.

    The construction of X uses a special Hartshorne-Rao module M.
  CannedExample
    i11 : betti tateResolutionOfSurface X

                  -1  0  1  2 3 4  5  6  7
    o11 = total: 104 61 30 10 3 5 10 32 84
             -4:   1  .  .  . . .  .  .  .
             -3: 103 61 30 10 . .  .  .  .
             -2:   .  .  .  . 2 .  .  .  .
             -1:   .  .  .  . 1 5  5  .  .
              0:   .  .  .  . . .  5 32 84

    o11 : BettiTally
    i12 : M=moduleFromSchreyerSurface X;

    o12 : Ideal of P4
    i13 : minimalBetti M

                 0  1  2  3  4 5
    o13 = total: 1 10 22 28 20 5
              0: 1  .  .  .  . .
              1: . 10 15  2  . .
              2: .  .  7 26 20 5

    o13 : BettiTally
    i14 : tangentDimension M==36

    o14 = true
  
  Text
    Thus the space of good modules in the Grassmannian G(5,15) of dimension 50 is smooth of
    the expected codimension 14 at our point M.
    Hence X lifts to a surface defined over some number field, yielding a surface over
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



doc///
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
    The function reads lists of precomputed H^1-modules and adjunction types.
  Example
    P4=ZZ/3[x_0..x_4];
    (Ms,types)=exampleOfSchreyerSurfaces P4;
    tally apply(Ms,M->minimalBetti M)
    netList apply(#Ms,i->(minimalBetti Ms_i, types_i))   
///
///
-- additional information
   P4=ZZ/3[x_0..x_4];
   (Ms,types)=exampleOfSchreyerSurfaces P4;
   tally apply(Ms,M->minimalBetti M)
   #Ms
   netList apply(#Ms,i->(minimalBetti Ms_i, types_i))  
   elapsedTime Xs=apply(9,i->schreyerSurfaceFromModule Ms_i); -- 665.508s elapsed
   #Xs
   netList apply(9,i->(X=Xs_i;
	   R=residualInQuintics X;
	   type=types_i;
	   s=#type;
	   curves=reverse flatten apply(sub((s-1)/2,ZZ),j->type_{2*j+1});
	   lastSurface=type_(s-1);
	   residual=tally (apply(decompose R,c->(dim c-1, degree c,
		   ( dim (c+X)-1,degree(c+X)))));
            (curves,lastSurface,residual))
	   )
-*
      +---------------------------------------------------------+
o46 = |({0, 0, 1, 5}, (10, 20, 11), Tally{(1, 1, (0, 6)) => 1 })|
      |                                   (1, 3, (0, 18)) => 1  |
      +---------------------------------------------------------+
      |({0, 0, 1, 4}, (7, 11, 5), Tally{(1, 1, (0, 6)) => 2 })  |
      |                                 (1, 2, (0, 12)) => 1    |
      +---------------------------------------------------------+
      |({4, 2, 1, 3}, (4, 4, 1), Tally{(1, 7, (0, 42)) => 1})   |
      +---------------------------------------------------------+
      |({3, 0, 2, 3}, (5, 6, 2), Tally{(1, 1, (0, 6)) => 2})    |
      |                                (2, 1, (1, 4)) => 1      |
      +---------------------------------------------------------+
      |({2, 2, 3, 2}, (3, 3, 1), Tally{(1, 2, (0, 12)) => 1})   |
      |                                (2, 2, (1, 8)) => 1      |
      +---------------------------------------------------------+
      |({8, 1, 3, 2}, (3, 2, 0), Tally{(1, 1, (0, 6)) => 1})    |
      |                                (2, 2, (1, 8)) => 1      |
      +---------------------------------------------------------+
      |({7, 4, 2, 2}, (2, 1, 0), Tally{(1, 2, (0, 12)) => 1})   |
      |                                (1, 3, (0, 18)) => 1     |
      |                                (2, 1, (1, 4)) => 1      |
      +---------------------------------------------------------+
      |({4, 4, 1}, (6, 7, 2), Tally{(1, 1, (0, 6)) => 1})       |
      |                             (2, 1, (1, 4)) => 3         |
      +---------------------------------------------------------+
      |({5, 6, 0}, (5, 5, 1), Tally{(2, 5, (1, 20)) => 1})      |
      +---------------------------------------------------------+
*-
   -- compare with the table for schreyer surfaces
///

-* for CannedExample in schreyerSurface

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
*-

doc///
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
    It searches for a suitable H^1-module with Hilbert function (1,5,5) and s >1 extra syzygies
    by searching in the
    codimension 6+2(s-2) subspace of modules with one extra syzygy, and computes the corresponding surface.
    To find an example, one has to check about 3^6 examples of modules.
  CannedExample
    i1 : P4=ZZ/3[x_0..x_4];
    i2 : setRandomSeed("find one fairly fast");
    -- setting random seed to 12449621278571636824524665417722879537212
    i3 : elapsedTime X=schreyerSurface(P4,2,Smooth=>false,Verbose=>true);
    modules tested = 267
    monads tested = 1
    -- 1.15894s elapsed

    o3 : Ideal of P4
    i4 : minimalBetti X

                0  1  2  3 4
    o4 = total: 1 12 26 20 5
             0: 1  .  .  . .
	     1: .  .  .  . .
	     2: .  .  .  . .
	     3: .  .  .  . .
	     4: .  5  .  . .
	     5: .  7 26 20 5

    o4 : BettiTally
    i5 : M=moduleFromSchreyerSurface X;

    o5 : Ideal of P4
    i6 : minimalBetti M

                0  1  2  3  4 5
    o6 = total: 1 10 22 28 20 5
             0: 1  .  .  .  . .
	     1: . 10 15  2  . .
	     2: .  .  7 26 20 5

    o6 : BettiTally
    i7 : setRandomSeed("also fairly fast");
    -- setting random seed to 113868634339878070906498645268872
    i8 : elapsedTime X=schreyerSurface(P4,3,Smooth=>false);
    -- .421701s elapsed

    o8 : Ideal of P4
    i9 : minimalBetti X

                0  1  2  3 4
    o9 = total: 1 13 27 20 5
             0: 1  .  .  . .
	     1: .  .  .  . .
	     2: .  .  .  . .
	     3: .  .  .  . .
	     4: .  5  1  . .
	     5: .  8 26 20 5

    o9 : BettiTally
    i10 : M=moduleFromSchreyerSurface X;

    o10 : Ideal of P4
    i11 : minimalBetti M

                 0  1  2  3  4 5
    o11 = total: 1 10 23 29 20 5
              0: 1  .  .  .  . .
	      1: . 10 15  3  . .
	      2: .  .  8 26 20 5

    o11 : BettiTally

SeeAlso
   findRandomSmoothSchreyerSurface
///

-* for CannedExample in findSchreyerSurface

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
*-

doc///
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
    codimension 8 subspace of modules with one extra syzygy, and computes the corresponding surface.
    To find an example one has to check about 3^8 examples of modules.
  CannedExample
    i1 : P4=ZZ/3[x_0..x_4];
    i2 : setRandomSeed("find one fairly fast");
    -- setting random seed to 12449621278571636824524665417722879537212
    i3 : elapsedTime X=findRandomSchreyerSurface P4;
    -- 1.04095s elapsed

    o3 : Ideal of P4
    i4 : minimalBetti X

                0  1  2  3 4
    o4 = total: 1 12 26 20 5
             0: 1  .  .  . .
	     1: .  .  .  . .
	     2: .  .  .  . .
	     3: .  .  .  . .
	     4: .  5  .  . .
	     5: .  7 26 20 5

    o4 : BettiTally
    i5 : M=moduleFromSchreyerSurface X;

    o5 : Ideal of P4
    i6 : minimalBetti M

                0  1  2  3  4 5
    o6 = total: 1 10 22 28 20 5
             0: 1  .  .  .  . .
	     1: . 10 15  2  . .
	     2: .  .  7 26 20 5

    o6 : BettiTally
    i7 : setRandomSeed("also fairly fast");
    -- setting random seed to 113868634339878070906498645268872
    i8 : elapsedTime X=findRandomSchreyerSurface(P4,3);
    -- .401666s elapsed

    o8 : Ideal of P4
    i9 : minimalBetti X

                0  1  2  3 4
    o9 = total: 1 13 27 20 5
             0: 1  .  .  . .
	     1: .  .  .  . .
	     2: .  .  .  . .
	     3: .  .  .  . .
	     4: .  5  1  . .
	     5: .  8 26 20 5

    o9 : BettiTally
    i10 : M=moduleFromSchreyerSurface X;

    o10 : Ideal of P4
    i11 : minimalBetti M

                 0  1  2  3  4 5
    o11 = total: 1 10 23 29 20 5
              0: 1  .  .  .  . .
	      1: . 10 15  3  . .
	      2: .  .  8 26 20 5

    o11 : BettiTally
  
SeeAlso
   findRandomSmoothSchreyerSurface
///
-* for CannedExample in findRandomSmoothSchreyerSurface
Example
    P4=ZZ/3[x_0..x_4];
    setRandomSeed("carefully choosen good randomSeed ");
    elapsedTime X=findRandomSmoothSchreyerSurface(P4,2);  
    minimalBetti X
    singX=X+minors(2,jacobian X);
    dim saturate singX==-1

*-


doc///
Key
 findRandomSmoothSchreyerSurface
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
    codimension 8 subspace of modules with one extra syzygy, and computes the corresponding surface
    and checks its smoothness. Since many H^1-modules lead to singular surfaces one has to check
    more then 3^8 examples of modules.
  CannedExample
    i1 : P4=ZZ/3[x_0..x_4];
    i2 : setRandomSeed("carefully choosen good randomSeed ");
    -- setting random seed to 138829667546446909693617136322436953342431360411403175217286822495497
    i3 : elapsedTime X=findRandomSmoothSchreyerSurface(P4,2);
    -- .305077s elapsed
    1
    -- 4.78983s elapsed

    o3 : Ideal of P4
    i4 : minimalBetti X

                0  1  2  3 4
    o4 = total: 1 12 26 20 5
             0: 1  .  .  . .
	     1: .  .  .  . .
	     2: .  .  .  . .
	     3: .  .  .  . .
	     4: .  5  .  . .
	     5: .  7 26 20 5

    o4 : BettiTally
    i5 : singX=X+minors(2,jacobian X);

    o5 : Ideal of P4
    i6 : dim saturate singX==-1

    o6 = true  
SeeAlso
   findRandomSchreyerSurface
///


doc///
Key
 collectSchreyerSurfaces
 (collectSchreyerSurfaces, List, List, Number, Number)
 (collectSchreyerSurfaces, List, List, Number)
Headline
 collect random smooth Schreyer surfaces
Usage
 (adj',Ms')= collectSchreyerSurfaces(adjTypes,Ms,s,N)
Inputs
 adjTypes:List
  of already discovered adjunction types
 Ms: List
    of ideals leading to the desired H^1-modules
 s:Number
  the number of desired extra syzygies
 N:Number
  the desired number of new modules
Outputs
 adj':List
  of adjunction types
 Ms' : List
  of modules
Description
  Text
    It searches for a suitable H^1-module with Hilbert function (1,5,5) and min(2,s) extra syzygies by searching in the
    codimension 8 subspace of modules with one extra syzygy, and computes the corresponding surface
    and checks its smoothness. Since many H^1-modules lead to singular surfaces one has to check
    more then 3^8 examples of modules.
  Example
    P4=ZZ/3[x_0..x_4];
    setRandomSeed("carefully choosen good randomSeed ");
    (Ms,adjTypes)=exampleOfSchreyerSurfaces P4;
    netList adjTypes
  Text
    The following command takes too much time.
  Example
    #Ms
    "elapsedTime (adj',Ms')=collectSchreyerSurfaces(adjTypes,Ms,2,1);"  
    
SeeAlso
   exampleOfSchreyerSurfaces
///
 -* for CannedExample tangentDimension
  Example
    P4=ZZ/3[x_0..x_4];
    (Ms,types)=exampleOfSchreyerSurfaces P4;
    elapsedTime netList apply(Ms,M->(minimalBetti M, tangentDimension M)) 
    --elapsedTime Xs=apply(Ms,M->schreyerSurfaceFromModule M); -- 192.472s elapsed
    --elapsedTime tally apply(Xs,X -> (singX=X+minors(2,jacobian X); dim saturate singX)) -- 54.9598s elapsed
*-

doc///
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
  CannedExample
    i1 : P4=ZZ/3[x_0..x_4];
    i2 : (Ms,types)=exampleOfSchreyerSurfaces P4;
    i3 : elapsedTime netList apply(Ms,M->(minimalBetti M, tangentDimension M))
    -- 7.88342s elapsed

         +----------------------------+
         |        0  1  2  3  4 5     |
    o3 = |(total: 1 10 22 28 20 5, 36)|
         |     0: 1  .  .  .  . .     |
	 |     1: . 10 15  2  . .     |
	 |     2: .  .  7 26 20 5     |
	 +----------------------------+
	 |        0  1  2  3  4 5     |
	 |(total: 1 10 22 28 20 5, 36)|
	 |     0: 1  .  .  .  . .     |
	 |     1: . 10 15  2  . .     |
	 |     2: .  .  7 26 20 5     |
	 +----------------------------+
	 |        0  1  2  3  4 5     |
	 |(total: 1 10 22 28 20 5, 36)|
	 |     0: 1  .  .  .  . .     |
	 |     1: . 10 15  2  . .     |
	 |     2: .  .  7 26 20 5     |
	 +----------------------------+
	 |        0  1  2  3  4 5     |
	 |(total: 1 10 22 28 20 5, 36)|
	 |     0: 1  .  .  .  . .     |
	 |     1: . 10 15  2  . .     |
	 |     2: .  .  7 26 20 5     |
	 +----------------------------+
	 |        0  1  2  3  4 5     |
	 |(total: 1 10 23 29 20 5, 34)|
	 |     0: 1  .  .  .  . .     |
	 |     1: . 10 15  3  . .     |
	 |     2: .  .  8 26 20 5     |
	 +----------------------------+
	 |        0  1  2  3  4 5     |
	 |(total: 1 10 23 29 20 5, 34)|
	 |     0: 1  .  .  .  . .     |
	 |     1: . 10 15  3  . .     |
	 |     2: .  .  8 26 20 5     |
	 +----------------------------+
	 |        0  1  2  3  4 5     |
	 |(total: 1 10 23 29 20 5, 34)|
	 |     0: 1  .  .  .  . .     |
	 |     1: . 10 15  3  . .     |
	 |     2: .  .  8 26 20 5     |
	 +----------------------------+
	 |        0  1  2  3  4 5     |
	 |(total: 1 10 24 30 20 5, 32)|
	 |     0: 1  .  .  .  . .     |
	 |     1: . 10 15  4  . .     |
	 |     2: .  .  9 26 20 5     |
	 +----------------------------+
	 |        0  1  2  3  4 5     |
	 |(total: 1 10 25 31 20 5, 30)|
	 |     0: 1  .  .  .  . .     |
	 |     1: . 10 15  5  . .     |
	 |     2: .  . 10 26 20 5     |
	 +----------------------------+
  Text
    This proves that the surfaces precomputed via exampleOfSchreyerSurfaces
    all lift to smooth surfaces over some algebraic number field (of characteristic 0).
///

-* Abo-Ranestad surfaces *-

-* for CannedExample of veroneseImagesInG25
 Example
    kk=ZZ/nextPrime 10^3; P4:=kk[x_0..x_4];
    n=7;
    elapsedTime (X,m4x2) = aboRanestadSurface(P4,n,Special=>2);
    (pts,vP2,vP3,g25)=veroneseImagesInG25(m4x2);
    (degree pts,degree vP2,degree vP3,degree g25)
    degree pts==n-1
    (L0,L1,L2,J)=adjunctionProcess(X,1);
    L0_1==n and degree pts==n-1;

*-


doc///
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
    In the Tate resolution of an Abo-Ranestad surface, there are a 4x2 matrix m4x2 and a 2x3 matrix m2x3
    with linear entries over the exterior algebra. These matrices define rational maps P3 -> G(2,5) and P2 -> G(2,5)
    and the type of the surface depends on how these images intersect in the Grassmannian G(2,5). It turns out that the number of
    (-1) lines on the surface will coincides with the number of intersection points of the images + 1.
    This function verifies this assertion in an example.
  CannedExample
    i2 :     kk=ZZ/nextPrime 10^3; P4:=kk[x_0..x_4];
    i4 :     n=7;
    i5 :     elapsedTime (X,m4x2) = aboRanestadSurface(P4,n,Special=>2);
     -- 6.14016s elapsed
    i6 :     (pts,vP2,vP3,g25)=veroneseImagesInG25(m4x2);
    i7 :     (degree pts,degree vP2,degree vP3,degree g25)

    o7 = (6, 4, 8, 5)
    o7 : Sequence
    i8 :     degree pts==n-1

    o8 = true
    i9 :     (L0,L1,L2,J)=adjunctionProcess(X,1);
    i10 :  L0_1==n and degree pts==n-1

    o110 = true
SeeAlso
   adjunctionProcessData
   aboRanestadSurface
///

-* 
for CannedExample of aboRanestadSurface
  Example
    kk=ZZ/nextPrime 10^3; e=symbol e; E=kk[e_0..e_4,SkewCommutative=>true];
    m2x3=matrix{{e_0,e_1,e_3},{e_1,e_2,e_4}}
  Text
    One can easily force 3 or 4 intersection points. To find more, we perform a random search over
    a finite ground field FF_q. Since an extra intersection point is a codimension 1 condition we can find
    examples with c additional intersection points with about q^c trials.
  Example
    P4=kk[x_0..x_4];
    elapsedTime (X,m4x2)=aboRanestadSurface(P4,4);  
    minimalBetti X
    singX=X+minors(2,jacobian X);
    dim saturate singX==-1
    (d,s)=(degree X, sectionalGenus X)
    LeBarzN6(d,s,1)==8
    Ksquare(d,s,1)==-12
    elapsedTime betti (T=tateResolutionOfSurface X)
    elapsedTime (numList,L1,L2,J)=adjunctionProcess(X,3);
    numList=={(4, 12, 13), 4, (12, 24, 13), 12, (12, 16, 5), 0, (4, 4, 1)}
  Text
    The last adjoint surface is a Del Pezzo surface of degree 4 in P4. Thus,
    X is the blow-up in 12+9 points embedded by a linear system of class
    (12;4^5,2^12,1^4).
  
  Text
    A special situation occurs when the 4x2 matrix m4x2 contains a 2x2 submatrix with entries in e_0..e_2 as well.
    In that case we have two conics in the e_0..e_2 plane which intersect in 4 points, hence four
    intersection points in the Grassmannian G(2,5).
    We can easily force 2 more intersection points  and can get a 7th intersection point via a
    codimension 1 random search.
  Example
    elapsedTime (X,m4x2)=aboRanestadSurface(P4,7,Special=>2);  
    minimalBetti X
    elapsedTime (numList,L1,L2,J)=adjunctionProcess(X,3);
    numList=={(4, 12, 13), 7, (12, 24, 13), 4, (12, 19, 8), 5, (7, 8, 2)}
    kk=ZZ/19;P4=kk[x_0..x_4];
    setRandomSeed("fast search");
    elapsedTime (X,m4x2)=aboRanestadSurface(P4,6,Special=>0,Verbose=>true);
    minimalBetti X
    elapsedTime (numList,L1,L2,J)=adjunctionProcess(X,3);
    numList=={(4, 12, 13), 6, (12, 24, 13), 6, (12, 18, 7), 6, (6, 6, 1)}
    setRandomSeed("another fast search");
    elapsedTime (X,m4x2)=aboRanestadSurface(P4,8,Special=>2,Verbose=>true); 
    minimalBetti X
    elapsedTime (L0,L1,L2,J)=adjunctionProcess(X,3);
    L0=={(4, 12, 13), 8, (12, 24, 13), 1, (12, 20, 9), 8, (8, 9, 2)}
  
  
*-

doc///
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
    In the Tate resolution of an Abo-Ranestad surface, there are a 4x2 matrix m4x2 and a 2x3 matrix m2x3
    with linear entries over the exterior algebra. These matrices define rational maps P3 -> G(2,5) and P2 -> G(2,5)
    and the type of the surface depends on how these images intersect in the Grassmannian G(2,5). It turns out that the number of
    (-1) lines on the surface will coincides with the number of intersection points of the images plus 1.
    We need at least 3 intersection points and can have up to 7 
    In the construction, we normalize the matrix m2x3 as indicated below.
  CannedExample
    i1 : kk=ZZ/nextPrime 10^3; e=symbol e; E=kk[e_0..e_4,SkewCommutative=>true];
    i4 : m2x3=matrix{{e_0,e_1,e_3},{e_1,e_2,e_4}}

    o4 = | e_0 e_1 e_3 |
         | e_1 e_2 e_4 |

                 2      3
    o4 : Matrix E  <-- E
  Text
    One can easily force 3 or 4 intersection points.
    To find more, we perform a random search over a finite ground field FF_q. Since an extra intersection point is a codimension-1 condition we can find examples with c additional intersection points with about q^c trials.
  CannedExample
    i5 : P4=kk[x_0..x_4];
    i6 : elapsedTime (X,m4x2)=aboRanestadSurface(P4,4);
    -- 4.81344s elapsed
    i7 : minimalBetti X

                0 1  2  3 4
    o7 = total: 1 9 18 13 3
             0: 1 .  .  . .
	     1: . .  .  . .
	     2: . .  .  . .
	     3: . .  .  . .
	     4: . 5  .  . .
	     5: . 4 18 13 3

    o7 : BettiTally
    i8 : singX=X+minors(2,jacobian X);

    o8 : Ideal of P4
    i9 : dim saturate singX==-1

    o9 = true
    i10 : (d,s)=(degree X, sectionalGenus X)

    o10 = (12, 13)

    o10 : Sequence
    i11 : LeBarzN6(d,s,1)==8

    o11 = true
    i12 : Ksquare(d,s,1)==-12

    o12 = true
    i13 : elapsedTime betti (T=tateResolutionOfSurface X)
    -- 17.9288s elapsed

                  -1  0  1  2 3 4 5  6  7
    o13 = total: 122 73 37 13 4 4 8 29 77
             -4:   1  .  .  . . . .  .  .
	     -3: 121 73 37 13 . . .  .  .
	     -2:   .  .  .  . 4 2 .  .  .
	     -1:   .  .  .  . . 2 3  .  .
	      0:   .  .  .  . . . 5 29 77

    o13 : BettiTally
    i14 : elapsedTime (numList,L1,L2,J)=adjunctionProcess(X,3);
    -- 127.77s elapsed
    i15 : numList=={(4, 12, 13), 4, (12, 24, 13), 12, (12, 16, 5), 0, (4, 4, 1)}

    o15 = true
  Text
    The last adjoint surface is a Del Pezzo surface of degree 4 in P4. Thus, X is the blow-up in 12+9 points embedded by a linear system of class (12;4^5,2^12,1^4).

    A special situation occurs when the 4x2 matrix m4x2 contains a 2x2 submatrix with entries in e_0..e_2 as well. In that case we have two conics in the e_0..e_2 plane which intersect in 4 points, hence four intersection points in the Grassmannian G(2,5). We can easily force 2 more intersection points and can get a 7th intersection point via a codimension 1 random search.
  CannedExample
    i16 : elapsedTime (X,m4x2)=aboRanestadSurface(P4,7,Special=>2);
    -- 5.37867s elapsed
    i17 : minimalBetti X

                 0 1  2  3 4
    o17 = total: 1 9 18 13 3
              0: 1 .  .  . .
	      1: . .  .  . .
	      2: . .  .  . .
	      3: . .  .  . .
	      4: . 5  .  . .
	      5: . 4 18 13 3

    o17 : BettiTally
    i18 : elapsedTime (numList,L1,L2,J)=adjunctionProcess(X,3);
    -- 122.83s elapsed
    i19 : numList=={(4, 12, 13), 7, (12, 24, 13), 4, (12, 19, 8), 5, (7, 8, 2)}

    o19 = true
    i20 : kk=ZZ/19;P4=kk[x_0..x_4];
    i22 : setRandomSeed("fast search");
    -- setting random seed to 11374490907814143332492
    i23 : elapsedTime (X,m4x2)=aboRanestadSurface(P4,6,Special=>0,Verbose=>true);
    trials so far to get a surface = 12
    trials to get a smooth surface = 1
    -- 7.20331s elapsed
    i24 : minimalBetti X

                 0 1  2  3 4
    o24 = total: 1 9 18 13 3
              0: 1 .  .  . .
	      1: . .  .  . .
	      2: . .  .  . .
	      3: . .  .  . .
	      4: . 5  .  . .
	      5: . 4 18 13 3

    o24 : BettiTally
    i25 : elapsedTime (numList,L1,L2,J)=adjunctionProcess(X,3);
    -- 147.992s elapsed
    i26 : numList=={(4, 12, 13), 6, (12, 24, 13), 6, (12, 18, 7), 6, (6, 6, 1)}

    o26 = true
    i27 : setRandomSeed("another fast search");
    -- setting random seed to 117342191518550946866766190799857765377
    i28 : elapsedTime (X,m4x2)=aboRanestadSurface(P4,8,Special=>2,Verbose=>true);
    trials so far to get a surface = 3
    trials to get a smooth surface = 1
    -- 8.3556s elapsed
    i29 : minimalBetti X

                 0 1  2  3 4
    o29 = total: 1 9 18 13 3
              0: 1 .  .  . .
	      1: . .  .  . .
	      2: . .  .  . .
	      3: . .  .  . .
	      4: . 5  .  . .
	      5: . 4 18 13 3

    o29 : BettiTally
    i30 : elapsedTime (L0,L1,L2,J)=adjunctionProcess(X,3);
    -- 157.524s elapsed
    i31 : L0=={(4, 12, 13), 8, (12, 24, 13), 1, (12, 20, 9), 8, (8, 9, 2)}

    o31 = true 
SeeAlso
   adjunctionProcessData
///
-*  for CannedExample of matrixFromAboRanestadSurface
  Example
    kk=ZZ/19;
    P4=kk[x_0..x_4];
    setRandomSeed("fairly fast search")
    elapsedTime (X,m4x2)=aboRanestadSurface(P4,6,Special=>2,Verbose=>true);
    betti tateResolutionOfSurface X
    elapsedTime X=aboRanestadSurfaceFromMatrix(P4,m4x2,Verbose=>true);   
    m4x2'=matrixFromAboRanestadSurface X
    m4x2
    minors(2,sub(m4x2,vars P4))==minors(2,sub(m4x2',vars P4))

*-

doc///
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
    In the Tate resolution of an Abo-Ranestad surface, there are a 4x2 matrix m4x2 and a 2x3 matrix m2x3
    with linear entries over the exterior algebra. The 2x3 matrix is normalized. The function returns the
    4x2 matrix.
  CannedExample
    i2 :     kk=ZZ/19;
    i3 :     P4=kk[x_0..x_4];
    i4 :     setRandomSeed("fairly fast search")
     -- setting random seed to 1219487757425192677910281801934109671

    o4 = 1219487757425192677910281801934109671
    i5 :     elapsedTime (X,m4x2)=aboRanestadSurface(P4,6,Special=>2,Verbose=>true);
    trials so far to get a surface = 1       
    trials to get a smooth surface = 1
     -- 7.27749s elapsed
    i6 :   betti tateResolutionOfSurface X
    
                 -1  0  1  2 3 4 5  6  7
    o6 = total: 122 73 37 13 4 4 8 29 77
            -4:   1  .  .  . . . .  .  .
            -3: 121 73 37 13 . . .  .  .
            -2:   .  .  .  . 4 2 .  .  .
            -1:   .  .  .  . . 2 3  .  .
             0:   .  .  .  . . . 5 29 77
    o6 : BettiTally
    i7 :  elapsedTime X=aboRanestadSurfaceFromMatrix(P4,m4x2,Verbose=>true);   
    trials so far to get a surface = 1
    trials to get a smooth surface = 1
     -- 5.91285s elapsed

    o7 : Ideal of P4
    i8 :     m4x2'=matrixFromAboRanestadSurface X

    o8 = {-1} | -5e_0+e_1+9e_2-5e_3-9e_4  -4e_2-8e_3+4e_4    |
         {-1} | 7e_0-2e_1+5e_3-7e_4       5e_2-e_3-4e_4      |
         {-1} | -9e_0+5e_1-4e_3-6e_4      e_1-4e_2+9e_3+7e_4 |
         {-1} | -8e_0+5e_1+6e_2+4e_3+3e_4 e_0+9e_2-7e_4      |

                            4                 2
    o8 : Matrix (kk[e ..e ])  <-- (kk[e ..e ])
                     0   4             0   4
    i9 :     m4x2

    o9 = {-1} | -9e_0-5e_1+e_2            -4e_0+7e_1-5e_2           |
         {-1} | e_0-9e_2                  -3e_0-3e_1-e_2            |
         {-1} | -4e_0-2e_1-7e_2+8e_3-3e_4 -8e_0+5e_1+e_2-3e_3-5e_4  |
         {-1} | e_0+5e_1-2e_2-8e_3+8e_4   -5e_0-4e_1-3e_2-6e_3-7e_4 |

                            4                 2
    o9 : Matrix (kk[e ..e ])  <-- (kk[e ..e ])
                     0   4             0   4
    i10 :     minors(2,sub(m4x2,vars P4))==minors(2,sub(m4x2',vars P4))

    o10 = true
SeeAlso
   aboRanestadSurface
   aboRanestadSurfaceFromMatrix
///
-* for CannedExample of aboRanestadSurfaceFromMatrix
 Example
    kk=ZZ/19;
    P4=kk[x_0..x_4];
    setRandomSeed("fairly fast search")
    elapsedTime (X,m4x2)=aboRanestadSurface(P4,6,Special=>2,Verbose=>true);
    betti tateResolutionOfSurface X
    elapsedTime X=aboRanestadSurfaceFromMatrix(P4,m4x2,Verbose=>true);   
    m4x2'=matrixFromAboRanestadSurface X
    m4x2
    minors(2,sub(m4x2,vars P4))==minors(2,sub(m4x2',vars P4))
*-

doc///
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
    In the Tate resolution of an Abo-Ranestad surface, there are a 4x2 matrix m4x2 and a 2x3 matrix m2x3
    with linear entries over the exterior algebra. These matrices define rational maps P3 -> G(2,5)
    and P2 -> G(2,5)
    and the type of the surface depends on how these images intersect in the Grassmannian G(2,5). It turns out that the number of
    (-1)-lines on the surface coincides with the number of intersection points of the images plus 1.
    The function returns a corresponding surface X.
   CannedExample
    i2 :     kk=ZZ/19
    i3 :     P4=kk[x_0..x_4];
    i4 :     setRandomSeed("fairly fast search")
     -- setting random seed to 1219487757425192677910281801934109671

    o4 = 1219487757425192677910281801934109671
    i5 :     elapsedTime (X,m4x2)=aboRanestadSurface(P4,6,Special=>2,Verbose=>true);
    trials so far to get a surface = 1
    trials to get a smooth surface = 1
     -- 7.48173s elapsed
    i6 :     betti tateResolutionOfSurface X

                 -1  0  1  2 3 4 5  6  7
    o6 = total: 122 73 37 13 4 4 8 29 77
            -4:   1  .  .  . . . .  .  .
            -3: 121 73 37 13 . . .  .  .
            -2:   .  .  .  . 4 2 .  .  .
            -1:   .  .  .  . . 2 3  .  .
             0:   .  .  .  . . . 5 29 77
    o6 : BettiTally
    i7 :     elapsedTime X=aboRanestadSurfaceFromMatrix(P4,m4x2,Verbose=>true);   
    trials so far to get a surface = 1
    trials to get a smooth surface = 1
     -- 6.34168s elapsed

    o7 : Ideal of P4
    i8 :     m4x2'=matrixFromAboRanestadSurface X

    o8 = {-1} | -5e_0+e_1+9e_2-5e_3-9e_4  -4e_2-8e_3+4e_4    |
         {-1} | 7e_0-2e_1+5e_3-7e_4       5e_2-e_3-4e_4      |
         {-1} | -9e_0+5e_1-4e_3-6e_4      e_1-4e_2+9e_3+7e_4 |
         {-1} | -8e_0+5e_1+6e_2+4e_3+3e_4 e_0+9e_2-7e_4      |

                            4                 2
    o8 : Matrix (kk[e ..e ])  <-- (kk[e ..e ])
                     0   4             0   4
    i9 :     m4x2
    o9 = {-1} | -9e_0-5e_1+e_2            -4e_0+7e_1-5e_2           |
         {-1} | e_0-9e_2                  -3e_0-3e_1-e_2            |
         {-1} | -4e_0-2e_1-7e_2+8e_3-3e_4 -8e_0+5e_1+e_2-3e_3-5e_4  |
         {-1} | e_0+5e_1-2e_2-8e_3+8e_4   -5e_0-4e_1-3e_2-6e_3-7e_4 |

                            4                 2
    o9 : Matrix (kk[e ..e ])  <-- (kk[e ..e ])
                     0   4             0   4
    i10 :     minors(2,sub(m4x2,vars P4))==minors(2,sub(m4x2',vars P4))

    o10 = true
 
SeeAlso
   aboRanestadSurface
   matrixFromAboRanestadSurface
///
-* For CannedExample of specificAboRanestadSurfac
  Example
    kk=ZZ/19
    P4=kk[x_0..x_4]
    E=kk[e_0..e_4,SkewCommutative=>true]
    elapsedTime (X,L0)=specificAboRanestadSurface(P4,E,3);
    L0
    elapsedTime (numList,adjList,ptsList,J)=adjunctionProcess X;
    numList==L0
    B=new BettiTally from {(0,{0},0) => 1, (1,{2},2) => 5, (2,{3},3) => 5, (3,{5},5)=> 1}
    minimalBetti J == B

*-

doc///
Key
 specificAboRanestadSurface
 (specificAboRanestadSurface,PolynomialRing, Ring, Number)

Headline
 Get the k-th specific Abo-Ranestad surface 
Usage
 (X,adjL)=specificAboRanestadSurface(P4,E,k);
Inputs
 P4:PolynomialRing
   coordinateRinge of P4
 E: Ring
   the dual exterior algebra
 k:Number
  get example number k
Outputs
 X:Ideal
  the ideal of an Abo-Ranestad surface
 adjL: List
   precomputed adjunction data 
Description
  Text
    In the Tate resolution of an Abo-Ranestad surface, there is a 4x2 matrix m4x2.
    We compute a Abo-Ranestad surface of the k-th given matrix
  CannedExample
    i2 :     kk=ZZ/19;
    i3 :     P4=kk[x_0..x_4];
    i4 :     E=kk[e_0..e_4,SkewCommutative=>true];
    i5 :     elapsedTime (X,L0)=specificAboRanestadSurface(P4,E,3);
     -- 15.3768s elapsed
    i6 :     L0

    o6 = {(4, 12, 13), 4, (12, 24, 13), 12, (12, 16, 5), 0, (4, 4, 1)}
    o6 : List
    i7 :     elapsedTime (numList,adjList,ptsList,J)=adjunctionProcess X;
     -- 305.883s elapsed
    i8 :     numList==L0

    o8 = true
  Text
    The third adjoint surface is a Del Pezzo surface of degree 4.  X=P2(12;4^5,2^12,1^4); 
SeeAlso
   aboRanestadSurfaceFromMatrix
   adjunctionProcess
   tateResolutionOfSurface
///
-* For CannedExample of get4x2Matrix
  Example
    kk=ZZ/nextPrime 10^3
    P4=kk[x_0..x_4]
    E=kk[e_0..e_4,SkewCommutative=>true]
    m2x3=matrix{{e_0,e_1,e_3},{e_1,e_2,e_4}}
    m4x2=get4x2Matrix(m2x3,4)
    elapsedTime X=aboRanestadSurfaceFromMatrix(P4,m4x2,Verbose=>true);   
    elapsedTime betti(T=tateResolutionOfSurface X)
    elapsedTime (numList,adjList,ptsList,J)=adjunctionProcess X;
    numList=={(4, 12, 13), 5, (12, 24, 13), 9, (12, 17, 6), 3, (5, 5, 1)}
    B=new BettiTally from {(0,{0},0) => 1, (1,{2},2) => 5, (2,{3},3) => 5, (3,{5},5)=> 1}
    minimalBetti J == B
 
*-

doc///
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
    In the Tate resolution of an Abo-Ranestad surface, there is a 4x2 matrix m4x2 and a 2x3 matrix m2x3
    with linear entries over the exterior algebra. These matrices define rational maps P3 -> G(2,5) and P2 -> G(2,5)
    and the type of the surface depends on how these images intersect in the Grassmannian G(2,5).
    It turns out that the number of
    (-1) lines on the surface will coincides with the number of intersection points of the images plus 1.
    The function returns for the normalized 2x3 matrix the desired 4x2 matrix.
  CannedExample
    i2 :     kk=ZZ/nextPrime 10^3

    o2 = kk
    o2 : QuotientRing
    i3 :     P4=kk[x_0..x_4]

    o3 = P4
    o3 : PolynomialRing
    i4 :     E=kk[e_0..e_4,SkewCommutative=>true]

    o4 = E
    o4 : PolynomialRing, 5 skew commutative variable(s)
    i5 :     m2x3=matrix{{e_0,e_1,e_3},{e_1,e_2,e_4}}

    o5 = | e_0 e_1 e_3 |
         | e_1 e_2 e_4 |
                 2      3
    o5 : Matrix E  <-- E
    i6 :     m4x2=get4x2Matrix(m2x3,4)

    o6 = {-1} | 117e_0+279e_1+228e_2-407e_3+484e_4 494e_0+126e_1+344e_2-261e_3+270e_4 |
         {-1} | -151e_0-122e_1+27e_2+472e_3-58e_4  495e_0-38e_1+334e_2-271e_3+441e_4  |
         {-1} | 129e_0+171e_1-280e_2-350e_3+264e_4 414e_0+369e_1+193e_2+50e_3-9e_4    |
         {-1} | 473e_0-56e_1+294e_2+456e_3-398e_4  -12e_0-392e_1-365e_2+462e_3-55e_4  |
                 4      2
    o6 : Matrix E  <-- E
    i7 :     elapsedTime X=aboRanestadSurfaceFromMatrix(P4,m4x2,Verbose=>true);   
    trials so far to get a surface = 1
    trials to get a smooth surface = 1
     -- 6.56431s elapsed

    o7 : Ideal of P4
    i8 :     elapsedTime betti(T=tateResolutionOfSurface X)
     -- 26.8608s elapsed

                 -1  0  1  2 3 4 5  6  7
    o8 = total: 122 73 37 13 4 4 8 29 77
            -4:   1  .  .  . . . .  .  .
            -3: 121 73 37 13 . . .  .  .
            -2:   .  .  .  . 4 2 .  .  .
            -1:   .  .  .  . . 2 3  .  .
             0:   .  .  .  . . . 5 29 77
    o8 : BettiTally
    i9 :     elapsedTime (numList,adjList,ptsList,J)=adjunctionProcess X;
     -- 254.72s elapsed
    i10 :     numList=={(4, 12, 13), 5, (12, 24, 13), 9, (12, 17, 6), 3, (5, 5, 1)}

    o10 = true
    i11 :     B=new BettiTally from {(0,{0},0) => 1, (1,{2},2) => 5, (2,{3},3) => 5, (3,{5},5)=> 1}

                 0 1 2 3
    o11 = total: 1 5 5 1
              0: 1 . . .
              1: . 5 5 .
              2: . . . 1
    o11 : BettiTally
    i12 :     minimalBetti J == B

    o12 = true
  Text
    The third adjoint surface is a Del Pezzo surface of degree 5.   X=P2(12;4^4,3^3,2^9,1^5);
SeeAlso
   aboRanestadSurfaceFromMatrix
   adjunctionProcess
   tateResolutionOfSurface
///


///
ci=ideal(gens X*random(source gens X,P4^{2:-5}));
Y=ci:X;
minimalBetti Y
betti tateResolutionOfSurface Y
(d,sg)=(degree Y, sectionalGenus Y)
Ksquare(d,sg,4)
D1=canonicalDivisor Y;
D2=canonicalDivisor Y;
D3=canonicalDivisor Y;
baseLocus=saturate(D1+D2+D3)
degree baseLocus, genus baseLocus
R=residualInQuintics X;
R==baseLocus
degree baseLocus, genus baseLocus, selfIntersectionNumber(Y,baseLocus)
E1=D1:baseLocus;
dim E1, degree E1, genus E1, selfIntersectionNumber(Y,E1)
///


-* Abo surfaces *-
-* for CannedExample in aboSurfaceFromMatrix
  Example
    kk=ZZ/19
    P4=kk[x_0..x_4];
    E=kk[e_0..e_4,SkewCommutative=>true]
    m3x4=matrix {{7*e_0+3*e_1-7*e_2-8*e_3, -4*e_0+3*e_1-7*e_2-8*e_4, 5*e_0+6*e_1+2*e_2+9*e_3-4*e_4,
      -6*e_0-7*e_1+3*e_3-3*e_4}, {e_0-5*e_1-e_2+7*e_3, -e_0-4*e_1+7*e_2-2*e_4, -e_0-8*e_1+2*e_3-3*e_4,
      -7*e_0+3*e_1-9*e_2+6*e_3-6*e_4}, {8*e_0-2*e_1+3*e_2+6*e_3, 9*e_0-2*e_1-e_2-e_4,
      9*e_0-9*e_1+7*e_2+e_3+8*e_4, -e_0+7*e_1-8*e_2+8*e_3-8*e_4}}
    elapsedTime X=aboSurfaceFromMatrix(m3x4,P4);
    (d,sg)=(degree X, sectionalGenus X)
    B=betti tateResolutionOfSurface X
    xO=chiO(X)
    Ksquare(d,sg,xO)==-6
    HdotK(d,sg)==12
    LeBarzN6(d,sg,xO)
    minimalBetti X
    residual=residualInQuintics X;
    dim residual, degree residual
    cResidual=primaryDecomposition residual;
    tally apply(cResidual,c->(dim c, degree c, dim (c+X), degree (c+X)))
    D=canonicalDivisor X;
    degree D
    selfIntersectionNumber(X,D)
    cD=primaryDecomposition D;#cD
    tally apply(cD,c->(Oc=sheaf(P4^1/c); r=rank HH^0(Oc);
	(dim c,degree c,r)))
    partits=partitionOfCanonicalDivisorOfAboSurface(X,Verbose=>true)
*-

doc///
Key
 aboSurfaceFromMatrix
 (aboSurfaceFromMatrix,Matrix,Ring)
 [aboSurfaceFromMatrix,Verbose]
Headline
 construct a Abo surface, a K3 surface of degree 12 and sectional genus 13
Usage
 X= aboSurfaceFromMatrix(m3x4,P4)
Inputs
  m3x4:Matrix
    a 3x4 matrix with linear entries in the exterior algebra E
  P4:PolynomialRing
    coordinate ring of P4
Outputs
 X:Ideal
  of a Abo surface
Description
  Text
    In the Tate resolution of Abo surfaces there are linear 3x1 and linear 3x4 matrices.
    We assume that transpose m3x1= matrix{{e_0,e_1,e_2}}. Whether the given m3x4 matrix
    together with m3x1 leads to a smooth surface can be tested with testMatrix1.

    The resulting surfaces is either a K3-surfaces or an elliptic surface. If it is a K3 surface then
    it is a 6-points blow-up of a minimal modeland the degrees of the
    six exceptional divisors form a partition of 12 into 6 parts. In the example below, this is the partition
    {1,2,2,2,3}.
  CannedExample
    i1 : kk=ZZ/19

    o1 = kk

    o1 : QuotientRing
    i2 : P4=kk[x_0..x_4];
    i3 : E=kk[e_0..e_4,SkewCommutative=>true]

    o3 = E

    o3 : PolynomialRing, 5 skew commutative variable(s)
    i4 : m3x4=matrix {{7*e_0+3*e_1-7*e_2-8*e_3, -4*e_0+3*e_1-7*e_2-8*e_4, 5*e_0+6*e_1+2*e_2+9*e_3-4*e_4,
	    -6*e_0-7*e_1+3*e_3-3*e_4}, {e_0-5*e_1-e_2+7*e_3, -e_0-4*e_1+7*e_2-2*e_4, -e_0-8*e_1+2*e_3-3*e_4,
	    -7*e_0+3*e_1-9*e_2+6*e_3-6*e_4}, {8*e_0-2*e_1+3*e_2+6*e_3, 9*e_0-2*e_1-e_2-e_4,
	    9*e_0-9*e_1+7*e_2+e_3+8*e_4, -e_0+7*e_1-8*e_2+8*e_3-8*e_4}}

    o4 = | 7e_0+3e_1-7e_2-8e_3 -4e_0+3e_1-7e_2-8e_4 5e_0+6e_1+2e_2+9e_3-4e_4
         | e_0-5e_1-e_2+7e_3   -e_0-4e_1+7e_2-2e_4  -e_0-8e_1+2e_3-3e_4     
         | 8e_0-2e_1+3e_2+6e_3 9e_0-2e_1-e_2-e_4    9e_0-9e_1+7e_2+e_3+8e_4 
      ------------------------------------------------------------------------
          -6e_0-7e_1+3e_3-3e_4      |
          -7e_0+3e_1-9e_2+6e_3-6e_4 |
          -e_0+7e_1-8e_2+8e_3-8e_4  |

    3      4
    o4 : Matrix E  <-- E
    i5 : elapsedTime X=aboSurfaceFromMatrix(m3x4,P4);
    -- 22.7432s elapsed

    o5 : Ideal of P4
    i6 : (d,sg)=(degree X, sectionalGenus X)

    o6 = (12, 13)

    o6 : Sequence
    i7 : B=betti tateResolutionOfSurface X

                 -1  0  1  2 3 4 5  6  7
    o7 = total: 123 74 38 14 4 4 8 28 76
            -4:   1  .  .  . . . .  .  .
            -3: 122 74 38 14 1 . .  .  .
	    -2:   .  .  .  . 3 1 .  .  .
	    -1:   .  .  .  . . 3 4  .  .
	     0:   .  .  .  . . . 4 28 76

    o7 : BettiTally
    i8 : xO=chiO(X)

    o8 = 2
    i9 : Ksquare(d,sg,xO)==-6

    o9 = true
    i10 : HdotK(d,sg)==12

    o10 = true
    i11 : LeBarzN6(d,sg,xO)

    o11 = 7
    i12 : minimalBetti X

                 0  1  2  3 4
    o12 = total: 1 12 24 17 4
              0: 1  .  .  . .
	      1: .  .  .  . .
	      2: .  .  .  . .
	      3: .  .  .  . .
	      4: .  4  .  . .
	      5: .  8 24 17 4

    o12 : BettiTally
    i13 : residual=residualInQuintics X;

    o13 : Ideal of P4
    i14 : dim residual, degree residual

    o14 = (3, 1)

    o14 : Sequence
    i15 : cResidual=primaryDecomposition residual;
    i16 : tally apply(cResidual,c->(dim c, degree c, dim (c+X), degree (c+X)))

    o16 = Tally{(1, 3, 1, 1) => 1}
                (2, 1, 1, 6) => 3
                (3, 1, 2, 4) => 1

    o16 : Tally
    i17 : D=canonicalDivisor X;

    o17 : Ideal of P4
    i18 : degree D

    o18 = 12
    i19 : selfIntersectionNumber(X,D)

    o19 = -6
    i20 : cD=primaryDecomposition D;#cD

    o21 = 4
    i22 : tally apply(cD,c->(Oc=sheaf(P4^1/c); r=rank HH^0(Oc);
	    (dim c,degree c,r)))

    o22 = Tally{(2, 1, 1) => 1}
                (2, 3, 1) => 1
		(2, 4, 2) => 2

    o22 : Tally
    i23 : partits=partitionOfCanonicalDivisorOfAboSurface(X,Verbose=>true)

    o23 = {1, 2, 2, 2, 2, 3}

    o23 : List
  Text
    X=X_min(p1..p6) is a minimal K3 surface blown up in 6 points embedded by the
    linear system H = |(Hmin;3,2^4,1)|. The four (-1)-conics decompose into two Frobenius orbits
    of length 2 and 2 in this specific example.
SeeAlso
   partitionOfCanonicalDivisorOfAboSurface
   canonicalDivisor
   selfIntersectionNumber
   chiO
   Ksquare
   residualInQuintics
   LeBarzN6   
///
-* for CannedExample in testMatrix
  Example
    kk=ZZ/19
    P4=kk[x_0..x_4];
    E=kk[e_0..e_4,SkewCommutative=>true]
    m3x1=transpose matrix{{E_0,E_1,E_2}}
    m3x4=matrix {{7*e_0+3*e_1-7*e_2-8*e_3, -4*e_0+3*e_1-7*e_2-8*e_4, 5*e_0+6*e_1+2*e_2+9*e_3-4*e_4,
      -6*e_0-7*e_1+3*e_3-3*e_4}, {e_0-5*e_1-e_2+7*e_3, -e_0-4*e_1+7*e_2-2*e_4, -e_0-8*e_1+2*e_3-3*e_4,
      -7*e_0+3*e_1-9*e_2+6*e_3-6*e_4}, {8*e_0-2*e_1+3*e_2+6*e_3, 9*e_0-2*e_1-e_2-e_4,
      9*e_0-9*e_1+7*e_2+e_3+8*e_4, -e_0+7*e_1-8*e_2+8*e_3-8*e_4}}
    elapsedTime r1=testMatrix1(m3x4,P4)
    elapsedTime r2=testMatrix2(m3x4,P4)
    r1==r2+5
    elapsedTime singX=testMatrix(m3x4,P4)
  Text
    The matrix m3x4 gives rize to a surface if r>5.
  Example
    X= aboSurfaceFromMatrix(m3x4,P4);
    betti tateResolutionOfSurface X
    elapsedTime singX=testMatrix(m3x4,P4)
  Text
    The last function also checks whether there is a smooth surface with these matrices.
    For a general 3x4 matrix, we have r=5.
  Example
    setRandomSeed("really general");
    m3x4g=random(E^3,E^{4:-1});
    testMatrix1(m3x4g,P4)==5
*-

doc///
Key
 testMatrix
 (testMatrix,Matrix,Ring)
 [testMatrix,SingX]
 [testMatrix,Verbose]
 testMatrix1
 (testMatrix1,Matrix,Ring)
 [testMatrix1,SingX]
 [testMatrix1,Verbose]
 testMatrix2
 (testMatrix2,Matrix,Ring)
 [testMatrix2,Verbose]
 [testMatrix2,WithM3x13]
 [testMatrix2,WithX]
Headline
 test whether a 3x4 matrix with entries over the exterior algebra leads to an Abo surface
Usage
 r = testMatrix1(m3x4,P4)
 singX = testMatrix(m3x4,P4)
Inputs
  m3x4:Matrix
    a 3x4 matrix with linear entries in the exterior algebra E
  P4:PolynomialRing
    coordinate ring of P4
Outputs
 r:ZZ
  the rank of the crucial Hom space
 singX: Ideal
   ideal of the singular locus of an example of a surfaces from m3x4
Description
  Text
    In the Tate resolution of Abo surfaces, there are linear 3x1 and linear 3x4 matrices.
    We assume that the transpose of m3x1= matrix{{e_0,e_1,e_2}}. Whether the given m3x4 matrix
    together with the m3x1 matrix leads to a smooth surface can be tested with testMatrix1.
    We need that r1>5.
  CannedExample
    i1 : kk=ZZ/19

    o1 = kk

    o1 : QuotientRing
    i2 : P4=kk[x_0..x_4];
    i3 : E=kk[e_0..e_4,SkewCommutative=>true]

    o3 = E

    o3 : PolynomialRing, 5 skew commutative variable(s)
    i4 : m3x1=transpose matrix{{E_0,E_1,E_2}}

    o4 = {-1} | e_0 |
         {-1} | e_1 |
         {-1} | e_2 |

                 3      1
    o4 : Matrix E  <-- E
    i5 : m3x4=matrix {{7*e_0+3*e_1-7*e_2-8*e_3, -4*e_0+3*e_1-7*e_2-8*e_4, 5*e_0+6*e_1+2*e_2+9*e_3-4*e_4,
	    -6*e_0-7*e_1+3*e_3-3*e_4}, {e_0-5*e_1-e_2+7*e_3, -e_0-4*e_1+7*e_2-2*e_4, -e_0-8*e_1+2*e_3-3*e_4,
	    -7*e_0+3*e_1-9*e_2+6*e_3-6*e_4}, {8*e_0-2*e_1+3*e_2+6*e_3, 9*e_0-2*e_1-e_2-e_4,
	    9*e_0-9*e_1+7*e_2+e_3+8*e_4, -e_0+7*e_1-8*e_2+8*e_3-8*e_4}}

    o5 = | 7e_0+3e_1-7e_2-8e_3 -4e_0+3e_1-7e_2-8e_4 5e_0+6e_1+2e_2+9e_3-4e_4
         | e_0-5e_1-e_2+7e_3   -e_0-4e_1+7e_2-2e_4  -e_0-8e_1+2e_3-3e_4     
         | 8e_0-2e_1+3e_2+6e_3 9e_0-2e_1-e_2-e_4    9e_0-9e_1+7e_2+e_3+8e_4 
    ------------------------------------------------------------------------
          -6e_0-7e_1+3e_3-3e_4      |
          -7e_0+3e_1-9e_2+6e_3-6e_4 |
          -e_0+7e_1-8e_2+8e_3-8e_4  |

                 3      4
    o5 : Matrix E  <-- E
    i6 : elapsedTime r1=testMatrix1(m3x4,P4)
     -- .0334885s elapsed

    o6 = 6
    i7 : elapsedTime r2=testMatrix2(m3x4,P4)
     -- .0486689s elapsed

    o7 = 1
    i8 : r1==r2+5

    o8 = true
    i9 : elapsedTime singX=testMatrix(m3x4,P4)
    -- 16.2713s elapsed

    o9 = ideal (x  + 8x , x  - 7x , x  + 9x , x  - 3x )
                 3     4   2     4   1     4   0     4

    o9 : Ideal of P4

  Text
    The matrix m3x4 gives rize to a surface if r>5.
  CannedExample
    i10 : X= aboSurfaceFromMatrix(m3x4,P4);

    o10 : Ideal of P4
    i11 : betti tateResolutionOfSurface X

                  -1  0  1  2 3 4 5  6  7
    o11 = total: 123 74 38 14 4 4 8 28 76
             -4:   1  .  .  . . . .  .  .
	     -3: 122 74 38 14 1 . .  .  .
	     -2:   .  .  .  . 3 1 .  .  .
	     -1:   .  .  .  . . 3 4  .  .
	      0:   .  .  .  . . . 4 28 76

    o11 : BettiTally
    i12 : elapsedTime singX=testMatrix(m3x4,P4)
    -- 16.4333s elapsed

    o12 = ideal 1

    o12 : Ideal of P4
  Text   
    The last function also checks whether there is a smooth surface with these matrices.
    For a general 3x4 matrix, we have r=5.
  CannedExample
    i13 : setRandomSeed("really general");
    -- setting random seed to 13089166972629855410042251015
    i14 : m3x4g=random(E^3,E^{4:-1});

                  3      4
    o14 : Matrix E  <-- E
    i15 : testMatrix1(m3x4g,P4)==5

    o15 = true
SeeAlso
  aboSurfaceFromMatrix
  
///
///
B=betti(hom=Hom(coker m3x4,coker m3x1**E^{1},DegreeLimit=>2))
r=if member((0,{0},0),keys B) then B#(0,{0},0) else 0
kk=coefficientRing ring m3x4
c:=null;
genHomo=sum(r,i->(
	while (c=random kk; c==0) do ();c*hom_i));
m3x3=homomorphism genHomo
betti (m3x4=matrix(m3x1**E^{1}|m3x3))
betti (s1=syz m3x4)
s2=s1*((id_(E^{4:-1})||map(E^{5:-2},E^{4:-2},0))|random(source s1,E^{4:-2}))
betti (T1=res coker transpose s2)
betti (T2=res(coker transpose T1.dd_6,LengthLimit=>8))
X=saturate ideal syz symExt(T2.dd_8,P4);
minimalBetti X
dim X==3 and degree X==12 and sectionalGenus X ==13
needsPackage "FastMinors"
viewHelp "FastMinors"
elapsedTime regularInCodimension(2,P4/X)
elapsedTime (singX=singularLocus X; dim singX==0)


///
-*  For CannedExample of analyzeAboSurface
  Example
    kk=ZZ/nextPrime 10^4;
    P4=kk[x_0..x_4];
    E=kk[e_0..e_4,SkewCommutative=>true];
    setRandomSeed("fix decompositions");
    elapsedTime (X,m3x4)=abo111333Surface(P4,E,Verbose=>false);
    elapsedTime (K,residual)=analyzeAboSurface(X,Verbose=>false);
    K    
    cResidual=primaryDecomposition residual;
    tally apply(cResidual, c-> (dim c, degree c, betti c, dim(c+X), degree (c+X),
	    tally apply(primaryDecomposition(c+X),d->(dim d, degree d, degree radical d))))
    (d,sg,xO)=(12,13,2);
    Ksquare(d,sg,xO) == -#K    
    numberOfMinusOneLines=#select(K,d->d==1)
    numberOfSixSecants=sum(select(cResidual,c->dim c == 2 and degree (c+X)==6),d->degree d)
    LeBarzN6(d,sg,xO)==numberOfMinusOneLines+numberOfSixSecants
  Text
    In this example, X has four 6-secant lines. The intersection of these four lines
    with X decomposes into Frobenius orbits of length (1,5) (twice), length (1,1,2,2)
    and length (6) respectively.
  Example  
    R=(select(cResidual,c->degree c==4))_0;-- a rational normal curve of degree 4
    minimalBetti R
    saturate ideal singularLocus R
    degree (R+X)==21


*-

doc///
Key
 analyzeAboSurface
 (analyzeAboSurface,Ideal)
 (analyzeAboSurface,Ring)
 (analyzeAboSurface,ZZ,Ring)
 [analyzeAboSurface,PrintConstructionData]
 [analyzeAboSurface,Verbose]
Headline
 analyze Abo surface
Usage
 (K,residual) = analyzeAboSurface X
 (K,residual) = analyzeAboSurface P4
 (K,residual) = analyzeAboSurface(n,P4)
Inputs
  X:Ideal
    of an Abo surface
  P4:PolynomialRing
    coordinate ring of P4
  n: ZZ
    number of random Abo surfaces to be analyzed
Outputs
 K:List
  the partition of the canonical divisor of X
 residual: Ideal
  the residualInQuintics ideal
Description
  Text
    We analyze the residual scheme to the input surface X in the scheme cut out
    by the quintic containing X and the partition of the canonical divisor of X
    in view of Le Barz's 6-secant formula.
  CannedExample 
    i1 : kk=ZZ/nextPrime 10^4;
    i2 : P4=kk[x_0..x_4];
    i3 : E=kk[e_0..e_4,SkewCommutative=>true];
    i4 : setRandomSeed("fix decompositions");
    -- setting random seed to 1220442291374344711948625538118317179
    i5 : elapsedTime (X,m3x4)=abo111333Surface(P4,E,Verbose=>false);
    -- 8.72264s elapsed
    i6 : elapsedTime (K,residual)=analyzeAboSurface(X,Verbose=>false);
    -- 5.28245s elapsed
    i7 : K

    o7 = {1, 1, 1, 3, 3, 3}

    o7 : List
    i8 : cResidual=primaryDecomposition residual;
    i9 : tally apply(cResidual, c-> (dim c, degree c, betti c, dim(c+X), degree (c+X),
	    tally apply(primaryDecomposition(c+X),d->(dim d, degree d, degree radical d))))

                             0 1
    o9 = Tally{(2, 1, total: 1 3, 1, 6, Tally{(1, 1, 1) => 1}) => 2   }
                          0: 1 3              (1, 5, 5) => 1
                             0 1
               (2, 1, total: 1 3, 1, 6, Tally{(1, 1, 1) => 2}) => 1
                          0: 1 3              (1, 2, 2) => 2
                             0 1
               (2, 1, total: 1 3, 1, 6, Tally{(1, 6, 6) => 1}) => 1
                          0: 1 3
                             0 1
               (2, 4, total: 1 6, 1, 21, Tally{(1, 1, 1) => 2  }) => 1
                          0: 1 .               (1, 3, 3) => 2
                          1: . 6               (1, 13, 13) => 1

    o9 : Tally
    i10 : (d,sg,xO)=(12,13,2);
    i11 : Ksquare(d,sg,xO) == -#K

    o11 = true
    i12 : numberOfMinusOneLines=#select(K,d->d==1)

    o12 = 3
    i13 : numberOfSixSecants=sum(select(cResidual,c->dim c == 2 and degree (c+X)==6),d->degree d)

    o13 = 4
    i14 : LeBarzN6(d,sg,xO)==numberOfMinusOneLines+numberOfSixSecants

    o14 = true
  Text
    In this example, X has four 6-secant lines. The intersection of these four lines
    with X decomposes into Frobenius orbits of length (1,5) (twice), length (1,1,2,2)
    and length (6) respectively.
  CannedExample
    i15 : R=(select(cResidual,c->degree c==4))_0;-- a rational normal curve of degree 4

    o15 : Ideal of P4
    i16 : minimalBetti R

                 0 1 2 3
    o16 = total: 1 6 8 3
              0: 1 . . .
              1: . 6 8 3

    o16 : BettiTally
    i17 : saturate ideal singularLocus R

    o17 = ideal 1

    o17 : Ideal of P4
    i18 : degree (R+X)==21

    o18 = true

  Text
    Since the rational normal curve R intersects X in 21>20 points,
    it is contained in any quintic of X.
SeeAlso
  LeBarzN6
  residualInQuintics
///
-* For CannedExample of partitionOfCanonicalDivisorOfAboSurface
  Example
    kk=ZZ/nextPrime 10^4;
    P4=kk[x_0..x_4];
    E=kk[e_0..e_4,SkewCommutative=>true];
    setRandomSeed("fix decompositions");
    elapsedTime (X,m3x4)=abo111333Surface(P4,E,Verbose=>false);
    elapsedTime K = partitionOfCanonicalDivisorOfAboSurface X   
    (d,sg,xO)=(12,13,2);
    Ksquare(d,sg,xO) , -#K
    HdotK(d,sg), sum K

*-

doc///
Key
 partitionOfCanonicalDivisorOfAboSurface
 (partitionOfCanonicalDivisorOfAboSurface,Ideal)
 [partitionOfCanonicalDivisorOfAboSurface,Equations]
 [partitionOfCanonicalDivisorOfAboSurface,Verbose]
Headline
 compute the partition of the canonical divisor
Usage
 K = partitionOfCanonicalDivisorOfAboSurface X
 IK = partitionOfCanonicalDivisorOfAboSurface(X,Equations=>true)
Inputs
  X:Ideal
    of an Abo surface  
Outputs
 K:List
  the partition of the canonical divisor of X
 IK: Ideal
  the homogeneous ideal of the canonical divisor
Description
  Text
    The canonical divisor of an Abo surface that is a non-minimal K3-surface, is a collection of
    six (-1)-curves of total degree 12. Which degrees occur depends on the surface.
  CannedExample
    i2 :     kk=ZZ/nextPrime 10^4;
    i3 :     P4=kk[x_0..x_4];
    i4 :     E=kk[e_0..e_4,SkewCommutative=>true];
    i5 :     setRandomSeed("fix decompositions");
      -- setting random seed to 1220442291374344711948625538118317179
    i6 :     elapsedTime (X,m3x4)=abo111333Surface(P4,E,Verbose=>false);
      -- 17.5693s elapsed
    i7 :     elapsedTime K = partitionOfCanonicalDivisorOfAboSurface X   
      -- 15.7959s elapsed

    o7 = {1, 1, 1, 3, 3, 3}
    o7 : List
    i8 :     (d,sg,xO)=(12,13,2);
    i9 :     Ksquare(d,sg,xO) , -#K

    o9 = (-6, -6)
    o9 : Sequence
    i10 :     HdotK(d,sg), sum K    

    o10 = (12, 12)
    o10 : Sequence
  Text
    The partitions of 12 into 6 parts are in bijection with the partitions of 6. From the
    11 partitions we have observed the following 9.
  Example
    #partitions(6)
    #{{1, 2, 2, 2, 2, 3}, {1, 1, 2, 2, 3, 3}, {1, 1, 1, 3, 3, 3}, {1, 1, 2, 2, 2, 4},	
      {1, 1, 1, 2, 3, 4}, {1, 1, 1, 2, 2, 5}, {1, 1, 1, 1, 4, 4}, {1, 1, 1, 1, 2, 6},
      {1, 1, 1, 1, 1, 7}}
  Text
   In some cases, the 6 points blown-up are infinitesimal near. We 
   think that these are boundary cases, which hence give no new families.
SeeAlso
  abo111333Surface
  abo111117Surface
  Ksquare
  HdotK
///

-* for CannedExample for abo112224Or111234Surface
 Example
    kk=ZZ/19;
    P4=kk[x_0..x_4];
    P3=kk[y_0..y_3];
    h=2
    setRandomSeed("get a 112224 surface in a minute");
    elapsedTime (X,m3x4,r)=abo112224Or111234Surface(P4,P3,h,Verbose=>true,Count=>true);
    partitionOfCanonicalDivisorOfAboSurface X == {1, 1, 2, 2, 2, 4}
    r
  Text
    Starting with a different random seed we find a surface of the second type.
  Example
    setRandomSeed("get a 111234 surface in a minute");
    elapsedTime (X,m3x4,r)=abo112224Or111234Surface(P4,P3,h,Verbose=>true,Count=>true);
    partitionOfCanonicalDivisorOfAboSurface X
 == {1, 1, 1, 2, 3, 4} 
    r
*-

doc///
Key
 abo112224Or111234Surface
 (abo112224Or111234Surface,Ring,Ring,ZZ)
 [abo112224Or111234Surface,Verbose]
 [abo112224Or111234Surface,Count]
Headline
 get an Abo surface of type {1,1,2,2,2,4} or {1,1,1,2,3,4} 
Usage
 (X,m3x4,r) = abo1112224Or111234(P4,P3,h)
Inputs
  P4:Ring
    coordinate ring of P4
  P3: Ring
    coordinate ring of P3
  h:ZZ
    desired dimension of the Hom space
Outputs
 X:Ideal
  ideal of an Abo surface X
 m3x4: Matrix
  the 3x4 matrix of linear forms over the exterior algebra
 r:ZZ
  dimension of the relevant Hom space
Description
  Text
    The function performs a search in a particular linear family of matrices.
    It finds matrices, we believe in codimesion 2, yielding smooth surfaces of two differnt components.
  CannedExample
    i1 : kk=ZZ/19;
    i2 : P4=kk[x_0..x_4];
    i3 : P3=kk[y_0..y_3];
    i4 : h=2

    o4 = 2
    i5 : setRandomSeed("get a 112224 surface in a minute");
    -- setting random seed to 14159357386601842985588153711132785285518962237126256200051594324
    i6 : elapsedTime (X,m3x4,r)=abo112224Or111234Surface(P4,P3,h,Verbose=>true,Count=>true);
    count= 14
    count1= 1
    -- 10.6815s elapsed
    i7 : partitionOfCanonicalDivisorOfAboSurface X == {1, 1, 2, 2, 2, 4}

    o7 = true
    i8 : r

    o8 = 2
  Text
    Starting with a different random seed we find a surface of the second type.
  CannedExample
    i9 : setRandomSeed("get a 111234 surface in a minute");
    -- setting random seed to 14159357386601842973017755919588831059697681095951739912610164124
    i10 : elapsedTime (X,m3x4,r)=abo112224Or111234Surface(P4,P3,h,Verbose=>true,Count=>true);
    count= 221
    count1= 1
    count= 412
    count1= 3
    count= 708
    count1= 4
    -- 54.3289s elapsed
    i11 : partitionOfCanonicalDivisorOfAboSurface X == {1, 1, 1, 2, 3, 4}

    o11 = true
    i12 : r

    o12 = 2
  Text
    The additional output under the Verbose=>true print the number of trails = count
    to get a matrix with HomSpace of dimension h which lead to a surface.
    With Option count=>true we print count1 which is 
    the number of times we got a not necessarily smooth surface.
    
    The codimension 2 believe is supported by the fact on average the value of count
    increases by approximately 180. 
SeeAlso
  LeBarzN6
  residualInQuintics
  partitionOfCanonicalDivisorOfAboSurface
  analyzeAboSurface
  aboSurfaceFromMatrix
///
-* For CannedExample of abo111144Surface
  Example
    kk=ZZ/nextPrime 10^4;
    P4=kk[x_0..x_4];
    P3=kk[y_0..y_3];
    setRandomSeed("quite fast");
    elapsedTime (X,m3x4,r)=abo111144Surface(P4,P3);
    r==4
    pK=partitionOfCanonicalDivisorOfAboSurface X
    R=residualInQuintics X;   
    cResidual=decompose R;
    tally apply(cResidual, c-> (dim c, degree c, (dim(c+X), degree (c+X))))	   
    (d,sg,xO)=(12,13,2);
    Ksquare(d,sg,xO) == -6    
    numberOfMinusOneLines=#select(pK,d->d==1)
    numberOfSixSecants=sum(select(cResidual,c->dim c == 2 and
	    degree (c+X)==6*degree c),c->degree c)
    LeBarzN6(d,sg,xO)==numberOfMinusOneLines+numberOfSixSecants
*-
doc///
Key
 abo111144Surface
 (abo111144Surface,Ring,Ring)
 [abo111144Surface,Verbose]
 [abo111144Surface,Count]
Headline
 get an Abo surface whose canonical divisors partitions into components of degrees {1,1,1,1,4,4}
 
Usage
 (X,m3x4,r) = abo111144Surface(P4,P3)
Inputs
  P4:Ring
    coordinate ring of P4
  P3: Ring
    coordinate ring of P3
Outputs
 X:Ideal
  ideal of an Abo surface X
 m3x4: Matrix
  the 3x4 matrix of linear forms over the exterior algebra
 r:ZZ
  dimension of the relevant Hom space
Description
  Text
    This gives an (apparantly) unirational construction of Abo surfaces with canonical divisor (1,1,1,1,4,4)
    from special (3x5) matrices over P3, such that the Bordiga surface is smooth and has
    seven rank two planes meeting the 1x3 line.
  CannedExample
    i2 :     kk=ZZ/nextPrime 10^4;
    i3 :     P4=kk[x_0..x_4];
    i4 :     P3=kk[y_0..y_3];
    i5 :     setRandomSeed("quite fast");
      -- setting random seed to 124864759781408404214
    i6 :     elapsedTime (X,m3x4,r)=abo111144Surface(P4,P3);
      -- 12.6696s elapsed
    i7 :  r==4

    o7 = true
    i8 : pK=partitionOfCanonicalDivisorOfAboSurface X

    o8 = {1, 1, 1, 1, 4, 4}
    o8 : List
    i9 :     R=residualInQuintics X;   

    o9 : Ideal of P4
    i10 :     cResidual=decompose R;
    i11 :     tally apply(cResidual, c-> (dim c, degree c, (dim(c+X), degree (c+X))))	   

    o11 = Tally{(2, 1, (1, 6)) => 3 }
                (2, 2, (1, 11)) => 2
    o11 : Tally
    i12 :     (d,sg,xO)=(12,13,2);
    i13 :     Ksquare(d,sg,xO) == -6    

    o13 = true
    i14 :     numberOfMinusOneLines=#select(pK,d->d==1)

    o14 = 4
    i15 :     numberOfSixSecants=sum(select(cResidual,c->dim c == 2 and
        	    degree (c+X)==6*degree c),c->degree c)

    o15 = 3
    i16 :     LeBarzN6(d,sg,xO)==numberOfMinusOneLines+numberOfSixSecants

    o16 = true
  Text
    In this example, X has three 6-secant lines and two 11-secant conics.
SeeAlso
  LeBarzN6
  residualInQuintics
  partitionOfCanonicalDivisorOfAboSurface
  analyzeAboSurface
  aboSurfaceFromMatrix
///
-*
For CannedExample of abo111333Surface
  Example
    kk=ZZ/nextPrime 10^4;
    P4=kk[x_0..x_4];
    E=kk[e_0..e_4,SkewCommutative=>true];
    setRandomSeed("fix decompositions");
    elapsedTime (X,m3x4)=abo111333Surface(P4,E,Verbose=>false);
    elapsedTime (K,residual)=analyzeAboSurface(X,Verbose=>false);
    K    
    cResidual=primaryDecomposition residual;
    tally apply(cResidual, c-> (dim c, degree c, betti c, dim(c+X), degree (c+X),
	    tally apply(primaryDecomposition(c+X),d->(dim d, degree d, degree radical d))))
    (d,sg,xO)=(12,13,2);
    Ksquare(d,sg,xO) == -#K    
    numberOfMinusOneLines=#select(K,d->d==1)
    numberOfSixSecants=sum(select(cResidual,c->dim c == 2 and degree (c+X)==6),d->degree d)
    LeBarzN6(d,sg,xO)==numberOfMinusOneLines+numberOfSixSecants


  Example
    R=(select(cResidual,c->degree c==4))_0;-- a rational normal curve of degree 4
    minimalBetti R
    saturate ideal singularLocus R
    degree (R+X)==21

*-

doc///
Key
 abo111333Surface
 (abo111333Surface,Ring,Ring)
 [abo111333Surface,Verbose]
Headline
 get an Abo surface whose canonical divisors partitions into components of degrees {1,1,1,3,3,3}
 
Usage
 (X,m3x4) = abo111333Surface(P4,E)

Inputs
  P4:Ring
    coordinate ring of P4
  E: Ring
    dual exterior algebra
Outputs
 X:Ideal
  ideal of an Abo surface X
 m3x4: Matrix
  the 3x4 matrix of linear forms over the exterior algebra
Description
  Text
    This gives an (apparently) unirational construction of Abo surfaces with 111333 partition
    of the canonical divisor. This function constructs a 3x4 matrix m3x4 with linear entries
    from E whose column space contains 7 rank-two planes meeting a specific line and returns
    aboSurfaceFromMatrix(m3x4,P4).
  CannedExample
    i2 :     kk=ZZ/nextPrime 10^4;
    i3 :     P4=kk[x_0..x_4];
    i4 :     E=kk[e_0..e_4,SkewCommutative=>true];
    i5 :     setRandomSeed("fix decompositions");
      -- setting random seed to 1220442291374344711948625538118317179
    i6 :     elapsedTime (X,m3x4)=abo111333Surface(P4,E,Verbose=>false);
      -- 14.5008s elapsed
    i7 :     elapsedTime (K,residual)=analyzeAboSurface(X,Verbose=>false);
      -- 13.6416s elapsed
    i8 :     K    

    o8 = {1, 1, 1, 3, 3, 3}
    o8 : List
    i9 :     cResidual=primaryDecomposition residual;
    i10 :     tally apply(cResidual, c-> (dim c, degree c, betti c, dim(c+X), degree (c+X),
        	    tally apply(primaryDecomposition(c+X),d->(dim d, degree d, degree radical d))))

                              0 1
    o10 = Tally{(2, 1, total: 1 3, 1, 6, Tally{(1, 1, 1) => 1}) => 2   }
                           0: 1 3              (1, 5, 5) => 1
                              0 1
                (2, 1, total: 1 3, 1, 6, Tally{(1, 1, 1) => 2}) => 1
                           0: 1 3              (1, 2, 2) => 2
                              0 1
                (2, 1, total: 1 3, 1, 6, Tally{(1, 6, 6) => 1}) => 1
                           0: 1 3
                              0 1
                (2, 4, total: 1 6, 1, 21, Tally{(1, 1, 1) => 2  }) => 1
                           0: 1 .               (1, 3, 3) => 2
                           1: . 6               (1, 13, 13) => 1
    o10 : Tally
    i11 :     (d,sg,xO)=(12,13,2);
    i12 :     Ksquare(d,sg,xO) == -#K    

    o12 = true
    i13 :     numberOfMinusOneLines=#select(K,d->d==1)

    o13 = 3
    i14 :     numberOfSixSecants=sum(select(cResidual,c->dim c == 2 and degree (c+X)==6),d->degree d)

    o14 = 4
    i15 :     LeBarzN6(d,sg,xO)==numberOfMinusOneLines+numberOfSixSecants

    o15 = true
  Text
    In this example, X has four 6-secant lines. The intersection of these lines
    with X decomposes into Frobenius orbits of length (1,5) (twice), length (1,1,2,2)
    and length (6) respectively.
  CannedExample
    i16 :     R=(select(cResidual,c->degree c==4))_0;-- a rational normal curve of degree 4

    o16 : Ideal of P4
    i17 :     minimalBetti R

                 0 1 2 3
    o17 = total: 1 6 8 3
              0: 1 . . .
              1: . 6 8 3

    o17 : BettiTally
    i18 :     saturate ideal singularLocus R

    o18 = ideal 1
    o18 : Ideal of P4
    i19 :     degree (R+X)==21

    o19 = true
  Text
    Since the rational normal curve R intersects X in 21>20 points,
    it is contained in any quintic of X.
SeeAlso
  LeBarzN6
  residualInQuintics
  partitionOfCanonicalDivisorOfAboSurface
  analyzeAboSurface
  aboSurfaceFromMatrix
///

-*
For CannedExample of abo111117Surface
  Example
    kk=ZZ/nextPrime 10^4;
    P4=kk[x_0..x_4];
    E=kk[e_0..e_4,SkewCommutative=>true];
    setRandomSeed("fix a fast decomposition of K");
    elapsedTime (X,m3x4)=abo111117Surface(P4,E,Verbose=>false);
    elapsedTime (K,residual)=analyzeAboSurface(X,Verbose=>false);
    K    
    cResidual=primaryDecomposition residual;
    netList apply(cResidual, c-> (dim c, degree c, betti c, dim(c+X), degree (c+X),
	    tally apply(primaryDecomposition(c+X),d->(dim d, degree d, degree radical d))))
    (d,sg,xO)=(12,13,2);
    Ksquare(d,sg,xO) == -#K    
    numberOfMinusOneLines=#select(K,d->d==1)
    expectedNumberOfSixSecants=LeBarzN6(d,sg,xO)-numberOfMinusOneLines
    plane=cResidual_0;
    cPlaneCapX=primaryDecomposition saturate(plane+X);
    point=(select(cPlaneCapX,c->dim c==1))_0;
    randomLineThroughPoint=trim(plane+ideal ((gens point)*random(source gens point,P4^{-1})));
    degree(randomLineThroughPoint+X)==6
    L1=cResidual_4;
    degree(L1+X)
    dim(L1+plane)
    tally apply(cResidual_{1,2,3},L->dim(L+plane))
*-

doc ///
Key
 abo111117Surface
 (abo111117Surface,Ring,Ring)
 [abo111117Surface,Verbose]
Headline
 get an Abo surface whose canonical divisors partitions into components of degrees {1,1,1,1,1,7}
 
Usage
 (X,m3x4) = abo111117Surface(P4,E)

Inputs
  P4:Ring
    coordinate ring of P4
  E: Ring
    dual exterior algebra
Outputs
 X:Ideal
  ideal of an Abo surface X
 m3x4: Matrix
  the 3x4 matrix of linear forms over the exterior algebra
Description
  Text
    This gives an (apparently) unirational construction of Abo surfaces with 111117 partition
    of the canonical divisor. This function constructs a 3x5 matrix m3x5 over the homogeneous coordinate ring of a P3 with linear enties such
    that it drops rank by two at a point and by two at the intersection of three lines in a plane, where
    its last 3x2 submatrix drops the rank by one.The functiom then defines m3x4 as
    the adjoint matrix of m3x5 and returns aboSurface(m3x4,P4). 
  CannedExample
    i2 :     kk=ZZ/nextPrime 10^4;
    i3 :     P4=kk[x_0..x_4];
    i4 :     E=kk[e_0..e_4,SkewCommutative=>true];
    i5 :     setRandomSeed("fix a fast decomposition of K");
     -- setting random seed to 13616088329504166732828826647070520602128631652395528887107
    i6 :     elapsedTime (X,m3x4)=abo111117Surface(P4,E,Verbose=>false);
     -- 10.9342s elapsed
    i7 :     elapsedTime (K,residual)=analyzeAboSurface(X,Verbose=>false);
     -- 12.8561s elapsed
    i8 :     K    

    o8 = {1, 1, 1, 1, 1, 7}
    o8 : List
    i9 :     cResidual=primaryDecomposition residual;
    i10 :  netList apply(cResidual, c-> (dim c, degree c, betti c, dim(c+X), degree (c+X),
        tally apply(primaryDecomposition(c+X),d->(dim d, degree d, degree radical d))))

          +--------------------------------------------------+
          |              0 1                                 |
    o10 = |(3, 1, total: 1 2, 2, 5, Tally{(1, 1, 1) => 1})   |
          |           0: 1 2              (2, 5, 5) => 1     |
          +--------------------------------------------------+
          |              0 1                                 |
          |(2, 1, total: 1 3, 1, 5, Tally{(0, 18, 1) => 1})  |
          |           0: 1 3              (1, 1, 1) => 3     |
          |                               (1, 2, 2) => 1     |
          +--------------------------------------------------+
          |              0 1                                 |
          |(2, 1, total: 1 3, 1, 5, Tally{(0, 19, 1) => 1})  |
          |           0: 1 3              (1, 1, 1) => 1     |
          |                               (1, 2, 2) => 2     |
          +--------------------------------------------------+
          |              0 1                                 |
          |(2, 1, total: 1 3, 1, 5, Tally{(0, 18, 1) => 1})  |
          |           0: 1 3              (1, 1, 1) => 3     |
          |                               (1, 2, 2) => 1     |
          +--------------------------------------------------+
          |              0 1                                 |
          |(2, 1, total: 1 3, 1, 6, Tally{(1, 1, 1) => 1})   |
          |           0: 1 3              (1, 2, 2) => 1     |
          |                               (1, 3, 3) => 1     |
          +--------------------------------------------------+
          |              0 1                                 |
          |(2, 2, total: 1 5, 1, 12, Tally{(1, 12, 12) => 1})|
          |           0: 1 1                                 |
          |           1: . 4                                 |
          +--------------------------------------------------+

    i11 :     (d,sg,xO)=(12,13,2);
    i12 :     Ksquare(d,sg,xO) == -#K    

    o12 = true
    i13 :     numberOfMinusOneLines=#select(K,d->d==1)

    o13 = 5
    i14 :     expectedNumberOfSixSecants=LeBarzN6(d,sg,xO)-numberOfMinusOneLines

    o14 = 2
    i15 :     plane=cResidual_0;

    o15 : Ideal of P4
    i16 :     cPlaneCapX=primaryDecomposition saturate(plane+X);
    i17 :     point=(select(cPlaneCapX,c->dim c==1))_0;

    o17 : Ideal of P4
    i18 :     randomLineThroughPoint=trim(plane+ideal ((gens point)*random(source gens point,P4^{-1})));

    o18 : Ideal of P4
    i19 :     degree(randomLineThroughPoint+X)==6

    o19 = true
    i20 :     L1=cResidual_4;

    o20 : Ideal of P4
    i21 :     degree(L1+X)

    o21 = 6
    i22 :     dim(L1+plane)

    o22 = 0
    i23 :     tally apply(cResidual_{1,2,3},L->dim(L+plane))

    o23 = Tally{1 => 3}
    o23 : Tally
  Text
    In this example, X has a pencil of 6-secant lines:
    All the lines in the plane through the point. Thus, LeBarz's 6-secant formula does not apply.
    There are three additional 6-secants lines one of which is L1.

    The 5-secant lines are contained in every quintic, because each intersects the plane at a point.
References
   \textit{Abo, H., Ranestad, K., Schreyer, F-O.} Non-general type surfaces in $\Pn 4$, an update, preprint (2026)    
SeeAlso
  LeBarzN6
  partitionOfCanonicalDivisorOfAboSurface
  analyzeAboSurface
///


-* For CannedExample of specificAboSurface
Example
    kk=ZZ/19;
    P4=kk[x_0..x_4];
    E=kk[e_0..e_4,SkewCommutative=>true];
    X=specificAboSurface(P4,E,1);
    minimalBetti X
    (d,sg)=(degree X, sectionalGenus X)
    Ksquare(d,sg,2)==-6   
    LeBarzN6(d,sg,2)==7
    pK=partitionOfCanonicalDivisorOfAboSurface X
    RX=residualInQuintics X;dim RX
    RX==radical RX
    tally apply(decompose RX,c->(dim c ,degree c, genus c,(dim (c+X),degree(c+X))))
  Text
    There are two (-1) lines and five 6-secant lines in this case.    
    The Tate resolution has a specific form:
  Example
    betti(T=tateResolutionOfSurface X)
    m3x4=T.dd_5^{0..2}_{4..7}
    m3x1=(transpose gens trim ideal T.dd_4^{0..2}_{3})**(ring T)^{-2}
    betti(hom=Hom(coker m3x4,coker m3x1,DegreeLimit=>0))
  Text
    The construction of X uses a special 3x4 matrix over E such
    that the Hom group above is non-zero.

    The (5,5) linked surface Y is an elliptic surface of degree 13 and sectional genus 16.
  Example
    setRandomSeed("get a Smooth Surface");
    betti(ci=ideal (gens X*random(source gens X,P4^{2:-5})))
    minimalBetti (Y=ci:X)
    RY=residualInQuintics Y;
    degree RY
    RY==canonicalDivisor X
    saturate ideal singularLocus (P4/Y) == ideal 1_P4
    D1=canonicalDivisor Y;
    D2=canonicalDivisor Y;
    betti(baseLocus=saturate (D1+D2))
    degree baseLocus, genus baseLocus
    selfIntersectionNumber(Y,baseLocus)
    (degree Y, sectionalGenus Y)==(13,16)
    betti tateResolutionOfSurface Y
    Ksquare(13,16,3)==-5
    LeBarzN6(13,16,3)==LeBarzN6(12,13,2)
    betti(E1=D1:baseLocus)
    degree E1, genus E1, selfIntersectionNumber(Y,E1)



*-


doc ///
Key
 specificAboSurface
 (specificAboSurface, Ring, Ring, Number)
 [specificAboSurface, Verbose]
Headline
 compute a specific smooth Abo surface
Usage
 X = specificAboSurface(P4,E,k)
Inputs
 P4:Ring
  coordinate ring of P4 over a ground field of small characteristic p
 E: Ring
  exterior algebra dual to P4.
 k: Number
  a number which  specifies the m3x4 matrix of linear forms over E to use. 
Outputs
 X:Ideal
  ideal of a Abo surface
Description
  Text
    In characteristic p=19 the function returns one of 9 specific Abo surfaces
    corresponding to one of the following partitions
    of the canonical divisor:

    {1, 2, 2, 2, 2, 3}, {1, 1, 2, 2, 3, 3}, {1, 1, 1, 3, 3, 3}, {1, 1, 2, 2, 2, 4},	
    {1, 1, 1, 2, 3, 4}, {1, 1, 1, 2, 2, 5}, {1, 1, 1, 1, 4, 4}, {1, 1, 1, 1, 2, 6},
    {1, 1, 1, 1, 1, 7}
   
    Other cases are p=11 and p=7.
  CannedExample
    i1 : kk=ZZ/19;
    i2 : P4=kk[x_0..x_4];
    i3 : E=kk[e_0..e_4,SkewCommutative=>true];
    i4 : X=specificAboSurface(P4,E,1);

    o4 : Ideal of P4
    i5 : minimalBetti X

                0  1  2  3 4
    o5 = total: 1 12 24 17 4
             0: 1  .  .  . .
	     1: .  .  .  . .
	     2: .  .  .  . .
	     3: .  .  .  . .
	     4: .  4  .  . .
	     5: .  8 24 17 4

    o5 : BettiTally
    i6 : (d,sg)=(degree X, sectionalGenus X)

    o6 = (12, 13)

    o6 : Sequence
    i7 : Ksquare(d,sg,2)==-6

    o7 = true
    i8 : LeBarzN6(d,sg,2)==7

    o8 = true
    i9 : pK=partitionOfCanonicalDivisorOfAboSurface X

    o9 = {1, 1, 2, 2, 3, 3}

    o9 : List
    i10 : RX=residualInQuintics X;dim RX

    o10 : Ideal of P4

    o11 = 2
    i12 : RX==radical RX

    o12 = true
    i13 : tally apply(decompose RX,c->(dim c ,degree c, genus c,(dim (c+X),degree(c+X))))

    o13 = Tally{(2, 1, 0, (1, 6)) => 1  }
              (2, 4, -3, (1, 24)) => 1

    o13 : Tally
  Text
    There are two (-1) lines and five 6-secant lines in this case.
    The Tate resolution has a specific form:
  CannedExample
    i14 : betti(T=tateResolutionOfSurface X)

                  -1  0  1  2 3 4 5  6  7
    o14 = total: 123 74 38 14 4 4 8 28 76
             -4:   1  .  .  . . . .  .  .
	     -3: 122 74 38 14 1 . .  .  .
	     -2:   .  .  .  . 3 1 .  .  .
	     -1:   .  .  .  . . 3 4  .  .
	      0:   .  .  .  . . . 4 28 76

    o14 : BettiTally
    i15 : m3x4=T.dd_5^{0..2}_{4..7}

    o15 = {3} | -e_0+5e_1+9e_2+5e_3+9e_4 -e_0-8e_1-6e_3-5e_4 
          {3} | -2e_0+7e_1-2e_2+2e_3     -2e_1+4e_2+7e_3-5e_4
          {3} | -2e_0+e_1-e_2-4e_3+7e_4  -5e_1-5e_2-6e_3-5e_4
          ------------------------------------------------------------------
	  2e_1+e_2-5e_3            9e_1+8e_2-3e_3-3e_4 |
	  -e_0+3e_1-7e_2+4e_3+7e_4 5e_1+e_2-8e_3+7e_4  |
	  8e_1+6e_2+7e_3           -e_0-9e_1+6e_2+e_3  |

                           3                 4
    o15 : Matrix (kk[e ..e ])  <-- (kk[e ..e ])
                      0   4             0   4
    i16 : m3x1=(transpose gens trim ideal T.dd_4^{0..2}_{3})**(ring T)^{-2}

    o16 = {1} | e_2 |
          {1} | e_1 |
          {1} | e_0 |

                           3                 1
    o16 : Matrix (kk[e ..e ])  <-- (kk[e ..e ])
                      0   4             0   4
    i17 : betti(hom=Hom(coker m3x4,coker m3x1,DegreeLimit=>0))

                 0  1
    o17 = total: 1 10
              0: 1  .
	      1: .  .
	      2: . 10

    o17 : BettiTally
  Text
    The construction of X uses a special 3x4 matrix over E such
    that the Hom group above is non-zero.

    The (5,5) linked surface Y is an elliptic surface of degree 13 and sectional genus 16.
  CannedExample
    i18 : setRandomSeed("get a Smooth Surface");
    -- setting random seed to 12565710742996174726728999654169754803660
    i19 : betti(ci=ideal (gens X*random(source gens X,P4^{2:-5})))

                 0 1
    o19 = total: 1 2
              0: 1 .
	      1: . .
	      2: . .
	      3: . .
	      4: . 2

    o19 : BettiTally
    i20 : minimalBetti (Y=ci:X)

                 0  1  2  3 4
    o20 = total: 1 12 22 14 3
              0: 1  .  .  . .
	      1: .  .  .  . .
	      2: .  .  .  . .
	      3: .  .  .  . .
	      4: .  3  .  . .
	      5: .  9 22 14 3

    o20 : BettiTally
    i21 : RY=residualInQuintics Y;

    o21 : Ideal of P4
    i22 : degree RY

    o22 = 12
    i23 : RY==canonicalDivisor X

    o23 = true
    i24 : saturate ideal singularLocus (P4/Y) == ideal 1_P4

    o24 = true
    i25 : D1=canonicalDivisor Y;

    o25 : Ideal of P4
    i26 : D2=canonicalDivisor Y;

    o26 : Ideal of P4
    i27 : betti(baseLocus=saturate (D1+D2))

                 0  1
    o27 = total: 1 15
               0: 1  .
	       1: .  .
	       2: . 15

    o27 : BettiTally
    i28 : degree baseLocus, genus baseLocus

    o28 = (5, -4)

    o28 : Sequence
    i29 : selfIntersectionNumber(Y,baseLocus)

    o29 = -5
    i30 : (degree Y, sectionalGenus Y)==(13,16)

    o30 = true
    i31 : betti tateResolutionOfSurface Y

                  -1  0  1  2 3 4 5  6  7
    o31 = total: 142 87 46 18 6 4 6 24 68
             -4:   1  .  .  . . . .  .  .
	     -3: 141 87 46 18 2 . .  .  .
	     -2:   .  .  .  . 4 3 .  .  .
	     -1:   .  .  .  . . 1 3  .  .
	      0:   .  .  .  . . . 3 24 68

    o31 : BettiTally
    i32 : Ksquare(13,16,3)==-5

    o32 = true
    i33 : LeBarzN6(13,16,3)==LeBarzN6(12,13,2)

    o33 = true
    i34 : betti(E1=D1:baseLocus)

                 0  1
    o34 = total: 1 22
              0: 1  .
	      1: .  .
	      2: .  .
	      3: . 22

    o34 : BettiTally
    i35 : degree E1, genus E1, selfIntersectionNumber(Y,E1)

    o35 = (12, 1, 0)

    o35 : Sequence
  Text
    The linked surface Y is a smooth elliptic surface blown-up in 5 points, which are (-1)-lines on Y
      
References
   \textit{Abo, H., Ranestad, K., Schreyer, F-O.} Non-general type surfaces in $\Pn 4$, an update, preprint (2026)

SeeAlso
   residualInQuintics
   tateResolutionOfSurface
   selfIntersectionNumber
   LeBarzN6
   Ksquare
   canonicalDivisor
   tateResolutionOfSurface
///

/// -* check the order of the specific examples of Abo surfaces
                   coincides with the order in the TeX file *-
    kk=ZZ/19;
    P4=kk[x_0..x_4];
    E=kk[e_0..e_4,SkewCommutative=>true];

    X=specificAboSurface(P4,E,0,Verbose=>true);-- 1,2,2,2,2,3
    minimalBetti X
    pK=partitionOfCanonicalDivisorOfAboSurface X
    RX=residualInQuintics X;
    tally apply(select(primaryDecomposition RX,c->dim c>1),c->(dim c-1, degree c,(dim(c+X)-1,degree (c+X))))

    X=specificAboSurface(P4,E,1,Verbose=>true);-- 1,1,2,2,3,3
    minimalBetti X
    pK=partitionOfCanonicalDivisorOfAboSurface X
    RX=residualInQuintics X;
    tally apply(select(primaryDecomposition RX,c->dim c>1),c->(dim c-1, degree c,(dim(c+X)-1,degree (c+X))))

    X=specificAboSurface(P4,E,2,Verbose=>true);-- 1,1,1,3,3,3
    pK=partitionOfCanonicalDivisorOfAboSurface X
    RX=residualInQuintics X;
    tally apply(select(primaryDecomposition RX,c->dim c>1),c->(dim c-1, degree c,(dim(c+X)-1,degree (c+X))))

    X=specificAboSurface(P4,E,3,Verbose=>true);-- 1,1,2,2,2,4
    pK=partitionOfCanonicalDivisorOfAboSurface X
    RX=residualInQuintics X;
    tally apply(select(primaryDecomposition RX,c->dim c>1),c->(dim c-1, degree c,(dim(c+X)-1,degree (c+X))))

    X=specificAboSurface(P4,E,4,Verbose=>true);-- 1,1,1,2,3,4
    pK=partitionOfCanonicalDivisorOfAboSurface X
    RX=residualInQuintics X;
    tally apply(select(primaryDecomposition RX,c->dim c>1),c->(dim c-1, degree c,(dim(c+X)-1,degree (c+X))))

    X=specificAboSurface(P4,E,5,Verbose=>true);-- 1,1,1,2,2,5
    pK=partitionOfCanonicalDivisorOfAboSurface X
    RX=residualInQuintics X;
    tally apply(select(primaryDecomposition RX,c->dim c>1),c->(dim c-1, degree c,(dim(c+X)-1,degree (c+X))))

    X=specificAboSurface(P4,E,6,Verbose=>true);-- 1,1,1,1,4,4
    pK=partitionOfCanonicalDivisorOfAboSurface X
    RX=residualInQuintics X;
    tally apply(select(primaryDecomposition RX,c->dim c>1),c->(dim c-1, degree c,(dim(c+X)-1,degree (c+X))))

    X=specificAboSurface(P4,E,7,Verbose=>true);-- 1,1,1,1,2,6
    pK=partitionOfCanonicalDivisorOfAboSurface X
    RX=residualInQuintics X;
    tally apply(select(primaryDecomposition RX,c->dim c>1),c->(dim c-1, degree c,(dim(c+X)-1,degree(c+X))))
    toString oo
    tally apply(select(primaryDecomposition RX,c->dim c>1),c->(dim c-1, degree c,
	    tally apply(decompose(c+X),d->(dim d-1,degree d)))
	)

    X=specificAboSurface(P4,E,8,Verbose=>true);-- 1,1,1,1,1,7
    pK=partitionOfCanonicalDivisorOfAboSurface X
    RX=residualInQuintics X;
    tally apply(select(primaryDecomposition RX,c->dim c>1),c->(dim c-1, degree c,(dim(c+X)-1,degree(c+X))))
    toString oo
    tally apply(select(primaryDecomposition RX,c->dim c>1),c->(dim c-1, degree c,
	    tally apply(decompose(c+X),d->(dim d-1,degree d)))
	)
-* order as desired;
 perhaps there is also a 1,1,1,1,3,5 case *-
    
///
-* For CannedExample of specificEllipticAboSurfaceD12S13
Example
    kk=ZZ/31;
    P4=kk[x_0..x_4];
    E=kk[e_0..e_4,SkewCommutative=>true];
    X=specificEllipticAboSurfaceD12S13(P4,E,0,Verbose=>true);
    (d,sg)=(degree X, sectionalGenus X)
    betti tateResolutionOfSurface X
    minimalBetti X
    K=canonicalDivisor X;
    cK=decompose K;
    tally apply(cK,c->(dim c, degree c, genus c, selfIntersectionNumber(X,c)))
*-

doc ///
Key
 specificEllipticAboSurfaceD12S13
 (specificEllipticAboSurfaceD12S13, Ring, Ring, Number)
 [specificEllipticAboSurfaceD12S13, Verbose]
Headline
 compute a specific smooth elliptic Abo surface
Usage
 X = specificEllipticAboSurfaceD12S13(P4,E,k)
Inputs
 P4:Ring
  coordinate ring of P4 over a ground field of characteristic 3
 E: Ring
  exterior algebra dual to P4.
 k: Number
  a number which  specifies the m3x4 matrix of linear forms over E to use. 
Outputs
 X:Ideal
  ideal of an Abo surface
Description
  Text
    In characteristic p=31 the function returns a non minimal elliptic surface with
    six (-1) curves of degrees {1,1,1,1,2,2}.
    The canonical divisor has in addition a component that is an elliptic curve of degree 4.
  CannedExample
    i2 :     kk=ZZ/31;
    i3 :     P4=kk[x_0..x_4];
    i4 :     E=kk[e_0..e_4,SkewCommutative=>true];
    i5 :     X=specificEllipticAboSurfaceD12S13(P4,E,0,Verbose=>true);
    #mdKRs = 1
    (K,R) = ({1, 1, 1, 1, 2, 2, 4}, Tally{(1, 1, (0, 6)) => 3   }), dim Hom = 6
                                          (2, 2, (1, 8, 9)) => 1
    o5 : Ideal of P4
    i6 :     (d,sg)=(degree X, sectionalGenus X)

    o6 = (12, 13)
    o6 : Sequence
    i7 :     betti tateResolutionOfSurface X

                 -1  0  1  2 3 4 5  6  7
    o7 = total: 123 74 38 14 4 4 8 28 76
            -4:   1  .  .  . . . .  .  .
            -3: 122 74 38 14 1 . .  .  .
            -2:   .  .  .  . 3 1 .  .  .
            -1:   .  .  .  . . 3 4  .  .
             0:   .  .  .  . . . 4 28 76
    o7 : BettiTally
    i8 :     minimalBetti X

                0  1  2  3 4
    o8 = total: 1 12 24 17 4
             0: 1  .  .  . .
             1: .  .  .  . .
             2: .  .  .  . .
             3: .  .  .  . .
             4: .  4  .  . .
             5: .  8 24 17 4
    o8 : BettiTally
    i9 :     K=canonicalDivisor X;
        
    o9 : Ideal of P4
    i10 : cK=decompose K;
    i11 :     tally apply(cK,c->(dim c, degree c, genus c, selfIntersectionNumber(X,c)))

    o11 = Tally{(2, 1, 0, -1) => 4 }
                (2, 4, -1, -2) => 1
                (2, 4, 1, 0) => 1
    o11 : Tally
  Text
    This surface is a non-minimal elliptic surface with four (-1)-lines and two (-1)-conics.
    The canonical divisor also has a degree 4 elliptic curve as a component.
References
   \textit{Abo, H., Ranestad, K., Schreyer, F-O.} Non-general type surfaces in $\Pn 4$, an update, preprint (2026)

SeeAlso
   residualInQuintics
   tateResolutionOfSurface
   selfIntersectionNumber
   LeBarzN6
   Ksquare
   canonicalDivisor
   tateResolutionOfSurface
///





///

kk=ZZ/19;
    P4=kk[x_0..x_4];
    E=kk[e_0..e_4,SkewCommutative=>true];
    X=specificAboSurface(P4,E,4);
    minimalBetti X
    saturate ideal singularLocus(P4/X)
    (d,sg)=(degree X, sectionalGenus X)
    Ksquare(d,sg,2)==-6   
    LeBarzN6(d,sg,2)==7
betti(T=tateResolutionOfSurface X)
betti(ci=ideal (gens X*random(source gens X,P4^{2:-5})))
    minimalBetti (Y=ci:X)
    RX=residualInQuintics X;
    RY=residualInQuintics Y;
    planes=select(decompose RX,c->dim c==3)
    minimalBetti(Y1=Y:planes_0)
    singY1=saturate ideal singularLocus(P4/Y1)
    dim singY1, degree singY1
    decompose singY1
    decompose Y1
    degree RY
    RY==canonicalDivisor X
    saturate ideal singularLocus (P4/Y)== ideal 1_P4
    D1=canonicalDivisor Y;
    D2=canonicalDivisor Y;
    betti(baseLocus=saturate (D1+D2))
    degree baseLocus, genus baseLocus
    selfIntersectionNumber(Y,baseLocus)
    (degree Y, sectionalGenus Y)==(13,16)
    betti tateResolutionOfSurface Y
    Ksquare(13,16,3)==-5
    LeBarzN6(13,16,3)==LeBarzN6(12,13,2)
    betti(E1=D1:baseLocus)
    degree E1, genus E1, selfIntersectionNumber(Y,E1)    

tally apply(decompose RY,c->(dim c-1, degree c,genus c,
		(dim(c+Y)-1, degree(c+Y)),selfIntersectionNumber(X,c)))
tally apply(select(decompose baseLocus,c->dim c ==2),c->(dim c -1, degree c, genus c,
	    selfIntersectionNumber(Y,c)))
    betti(E2=D2:baseLocus)
    degree E2, genus E2, selfIntersectionNumber(Y,E2)
    residualInQuintics X==baseLocus
    dim (E1+E2), degree(E1+E2)
///

-* for CannedExample of collectAboSurfaces
Example
    kk=ZZ/19;
    P4=kk[x_0..x_4];
    E=kk[e_0..e_4,SkewCommutative=>true];
    mdKRs={};
    setRandomSeed("carefully choosen randomSeed");
    elapsedTime mdKRs'=collectAboSurfaces(mdKRs,P4,E,1) -- 31.8852s elapsed

*-


doc ///
Key
 collectAboSurfaces
 (collectAboSurfaces, List, Ring, Ring, ZZ)
 [collectAboSurfaces,Verbose]
 [collectAboSurfaces,Special]
Headline
 collect Abo surfaces
Usage
 mdKR'= specificAboSurfaces(mdKRs,P4,E,N)
Inputs
 mdKRs: List
   of Abo surface data m3x4,d,(K,R)
 P4:Ring
  coordinate ring of P4 over a small finite ground field 
 E: Ring
  exterior algebra dual to P4.
 N: ZZ
  the desired total number of  surface data. 
Outputs
 mdKR':List
  of Abo surface data m3x4,d,(K,R)
Description
  Text
    The functions collects N examples of surface  by choosing randomly 3x4 matrices over the exterior
    algebra and testing whether they lead to a surface.
    If the pair of (K,R) of the partition of the canonical divisor and the numerical type of
    the residual scheme to the surface in the quintics containing it is new or for that type there are
    only few examples in the list then the
    the example will be appended to the current list. The functions stops when the total number N of
    examples is reached.
    
    With the option Special=>true then the m3x4 Bordiga matrix has a rank 1 point.
  CannedExample
    i2 :     kk=ZZ/19;
    i3 :     P4=kk[x_0..x_4];
    i4 :     E=kk[e_0..e_4,SkewCommutative=>true];
    i5 :     mdKRs={};
    i6 :     setRandomSeed("carefully choosen randomSeed");
     -- setting random seed to 130783826824055887938028823731402206818653657496837223808
    i7 :     elapsedTime mdKRs'=collectAboSurfaces(mdKRs,P4,E,1) 
      -- 13.0813s elapsed
        K = {1, 1, 1, 3, 3, 3}
        count1= 1
        count=1, (K,R)= ({1, 1, 1, 3, 3, 3}, Tally{((2, 1), (1, 6)) => 4 }), dim Hom = 1
                                                   ((2, 4), (1, 21)) => 1
        count1= 1
        -- 56.2178s elapsed
    o7 = {(| 6e_0-5e_1+e_2-9e_3   -8e_0-6e_1+7e_4     e_0+6e_1-3e_2+e_3+4e_4   
           | -9e_0-2e_1+8e_2+4e_3 e_0-3e_1-8e_2-6e_4  -3e_0-2e_1+4e_2+3e_3-7e_4
           | 7e_0-3e_1+e_2-6e_3   4e_0-3e_1-9e_2-6e_4 -8e_0+5e_1-8e_2          
         --------------------------------------------------------------------------
         2e_0+8e_1-4e_2-8e_3+8e_4 |, 1, ({1, 1, 1, 3, 3, 3}, Tally{((2, 1), (1,
         4e_0+4e_1-8e_2-e_3+e_4   |                                ((2, 4), (1,
         8e_0-3e_1+3e_2+7e_3-7e_4 |
         --------------------------------------------------------------------------
         6)) => 4 }))}
         21)) => 1
    o7 : List
  
SeeAlso
   residualInQuintics
   partitionOfCanonicalDivisorOfAboSurface
   
///

/// --prepare specificAboExample
kk=ZZ/11
P4=kk[x_0..x_4]
E=kk[e_0..e_4,SkewCommutative=>true]
elapsedTime minimalBetti (X=specificAboSurface(P4,E,9))

kk=ZZ/5
P4=kk[x_0..x_4]
E=kk[e_0..e_4,SkewCommutative=>true]
setRandomSeed("start from here");
mdKRs={}
elapsedTime mdKRs'=collectAboSurfaces(mdKRs,P4,E,20,Special=>true);#mdKRs'
elapsedTime mdKRs=collectAboSurfaces(mdKRs',P4,E,50);#mdKRs
#mdKRs
mdKRs= reverse sort(mdKRs , mdKR-> mdKR_2_0);
Ta=tally apply(mdKRs , mdKR-> mdKR_2_0)
netList apply(mdKRs,mdKR->(mdKR_1,mdKR_2))
pos=apply(reverse sort keys Ta,K->position(mdKRs,mdKR->K==mdKR_2_0))
toString mdKRs_pos
--     1) use cut and paste into specificAboSurface
--     2) replace e->E use replace nEw -> new
--     3) adapt the coments and error handling in specificAboSurface
#pos
kk=ZZ/7;
P4=kk[x_0..x_4];
E=kk[e_0..e_4,SkewCommutative=>true];
elapsedTime minimalBetti (X=specificAboSurface(P4,E,4))
elapsedTime apply(7,k->minimalBetti (X=specificAboSurface(P4,E,k)))


///
-* for CannedExample randomAboSurface
  Example
    kk=ZZ/7;
    P4=kk[x_0..x_4];
    E=kk[e_0..e_4,SkewCommutative=>true];    
    setRandomSeed("carefully choosen fast randomSeed");
    elapsedTime (X,m3x4)=randomAboSurface(P4,E);
    saturate minors(2,sub(m3x4,vars P4))
    setRandomSeed("same start");
    elapsedTime (Xs,m3x4s)=randomSpecialAboSurface(P4,E);
    pt=saturate minors(2,sub(m3x4s,vars P4))
    sub(m3x4s,vars P4)%pt
*-

doc ///
Key
 randomAboSurface
 randomSpecialAboSurface
 randomAboSurfaceWithLargeHomSpace
 randomAboSurfaceWithHomSpaceOfGivenDimension
 (randomAboSurface, Ring, Ring)
 [randomAboSurfaceWithLargeHomSpace,Verbose]
 [randomAboSurfaceWithLargeHomSpace,Count]
 [randomAboSurfaceWithHomSpaceOfGivenDimension,Verbose]
 [randomAboSurfaceWithHomSpaceOfGivenDimension,Count]
 [randomAboSurface,Verbose]
 [randomAboSurface,Count]
 (randomSpecialAboSurface, Ring, Ring)
 [randomSpecialAboSurface,Verbose]
 [randomSpecialAboSurface,Count]
 [randomSpecialAboSurface,PrintConstructionData]
 [randomAboSurface,PrintConstructionData]
Headline
 get random Abo surfaces
Usage
 (X,m3x4)=randomAboSurface(P4,E)
 (X,m3x4)=randomSpecialAboSurface(P4,E)
 (X,m3x4,r)=randomAboSurfaceWithLargeHomSpace(P4,E,h)
 (X,m3x4,r)=randomAboSurfaceWithLargeHomSpace(P4,E,h)
Inputs
 P4:Ring
  coordinate ring of P4 over a small finite ground field.
 E: Ring
  exterior algebra dual to P4
 h: ZZ
  dimension of the desired Hom-space, or a lower bound for that
Outputs
 X:Ideal
   of an Abo surface
 m3x4: Matrix
   3x4 matrix over the exterior algebra
 r:ZZ
  dimension of the Hom-space
   
Description
  Text
    The functions constructs an Abo surface by randomly choosing 3x4 matrices over the exterior
    algebra and testing whether they lead to a surface.
    
    In the case of randomSpecialAboSurface, the m3x4 Bordiga matrix has a rank 1 point.

    The two more specialized versions search for Abo surfaces with a lower bound or precise 
    dimension of the Hom space. These are search functions can take a long time.
  CannedExample
    i1 : kk=ZZ/7;
    i2 : P4=kk[x_0..x_4];
    i3 : E=kk[e_0..e_4,SkewCommutative=>true];
    i4 : setRandomSeed("carefully choosen fast randomSeed");
    -- setting random seed to 1374551163826207026669476597251851023179306320125668960254614211770
    i5 : elapsedTime (X,m3x4)=randomAboSurface(P4,E);
    -- 37.8333s elapsed
    i6 : saturate minors(2,sub(m3x4,vars P4))

    o6 = ideal 1

    o6 : Ideal of P4
    i7 : setRandomSeed("same start");
    -- setting random seed to 126835971200444596612
    i8 : elapsedTime (Xs,m3x4s)=randomSpecialAboSurface(P4,E);
    -- 21.6516s elapsed
    i9 : pt=saturate minors(2,sub(m3x4s,vars P4))

    o9 = ideal (x , x , x , x )
                 4   3   2   1

    o9 : Ideal of P4
    i10 : sub(m3x4s,vars P4)%pt

    o10 = | -2x_0 0 x_0 -3x_0 |
          | 0     0 0   0     |
          | 0     0 0   0     |

                   3       4
    o10 : Matrix P4  <-- P4


References
   \textit{Abo, H., Ranestad, K., Schreyer, F-O.} Non-general type surfaces in $\Pn 4$, an update, preprint (2026)       
SeeAlso
   residualInQuintics
   partitionOfCanonicalDivisorOfAboSurface
   
///
-* For CannedExample of randomEllipticAboSurface
Example
    kk=ZZ/19;
    P4=kk[x_0..x_4];
    P3=kk[y_0..y_3];
    setRandomSeed("fairly fast");
    elapsedTime (X,m3x4,r)=randomEllipticAboSurface(P4,P3);
    minimalBetti X
    (d,sg)=(degree X, sectionalGenus X)
    Ksquare(d,sg,2)
    betti(tateResolutionOfSurface X)
    RX=residualInQuintics X;
    cRX=decompose RX;
    tally apply(cRX, c-> (dim c -1, degree c, (dim(c+X)-1,degree(c+X))))
    K=canonicalDivisor X;
    cK=decompose K;
    tally apply(cK,c->(dim c -1, degree c, genus c, selfIntersectionNumber(X,c), minimalBetti c))


  Example
    E=(select(cK,c->genus c ==1))_0;
    betti E,
    saturate ideal singularLocus(P4/E)
    dim E,degree E, genus E, minimalBetti E
    m=2
    mE= saturate(E^m+X);
    betti mE
    H=ideal( gens mE*random(source gens mE,P4^{-6}));
    linked=saturate((H+X):mE);
    betti linked, betti saturate linked
    H'=ideal(gens linked*random(source gens linked,P4^{-6}));
    betti trim ideal(gens linked%X)
    betti linked, betti X
    E'=(X+H'):linked;
    betti E'
    degree E', genus E'
    dim(E'+E)
*-

doc ///
Key
 randomEllipticAboSurface
 (randomEllipticAboSurface, Ring, Ring)
 [randomEllipticAboSurface,Verbose]
 [randomEllipticAboSurface,Count]
 [randomEllipticAboSurface,PrintConstructionData]
 [randomEllipticAboSurface,NumberOfRank1Points]
Headline
 Get random elliptic Abo surface
Usage
 (X,m3x4,r)=randomEllipticAboSurface(P4,P3)
Inputs
 P4:Ring
  coordinate ring of P4 over a small finite ground field
 P3: Ring
  coordinate ring of a P3
Outputs
 X:Ideal
   of an Abo surface
 m3x4: Matrix
   over the exterior algebra dual P4
 r: ZZ
   rank of solution space, dimension of the Hom space is 115-r  
Description
  Text
    The functions constructs a random elliptic Abo surface by carefully choosing 
    a 3x5 matrix over P3 such that the adjoint Bordiga matrix has the desired number of rank 1 points.
    
    The fastest, hence default, choice is NumberOfRank1Points=>3.
  CannedExample
    i2 :     kk=ZZ/19;
    i3 :     P4=kk[x_0..x_4];
    i4 :     P3=kk[y_0..y_3];
    i5 :     setRandomSeed("fairly fast");
      -- setting random seed to 11374382488447926963809
    i6 :     elapsedTime (X,m3x4,r)=randomEllipticAboSurface(P4,P3);
      -- 21.0565s elapsed
    i7 :     minimalBetti X

                0  1  2  3 4
    o7 = total: 1 12 24 17 4
             0: 1  .  .  . .
             1: .  .  .  . .
             2: .  .  .  . .
             3: .  .  .  . .
             4: .  4  .  . .
             5: .  8 24 17 4
    o7 : BettiTally
    i8 :     (d,sg)=(degree X, sectionalGenus X)

    o8 = (12, 13)
    o8 : Sequence
    i9 :     Ksquare(d,sg,2)

    o9 = -6
    i10 :     betti(tateResolutionOfSurface X)
   

                  -1  0  1  2 3 4 5  6  7
    o10 = total: 123 74 38 14 4 4 8 28 76
             -4:   1  .  .  . . . .  .  .
             -3: 122 74 38 14 1 . .  .  .
             -2:   .  .  .  . 3 1 .  .  .
             -1:   .  .  .  . . 3 4  .  .
              0:   .  .  .  . . . 4 28 76
    o10 : BettiTally
    i11 :  RX=residualInQuintics X;

    o11 : Ideal of P4
    i12 :     cRX=decompose RX;
    i13 :     tally apply(cRX, c-> (dim c -1, degree c, (dim(c+X)-1,degree(c+X))))

    o13 = Tally{(1, 1, (0, 6)) => 3}
                (2, 2, (1, 8)) => 1
    o13 : Tally
    i14 :     K=canonicalDivisor X;

    o14 : Ideal of P4
    i15 :     cK=decompose K;
    i16 :     tally apply(cK,c->(dim c -1, degree c, genus c, selfIntersectionNumber(X,c), minimalBetti c))

                                      0 1 2 3 4
    o16 = Tally{(1, 2, -1, -2, total: 1 5 8 5 1) => 1}
                                   0: 1 1 . . .
                                   1: . 4 8 5 1
                                     0 1 2 3
                (1, 1, 0, -1, total: 1 3 3 1) => 2
                                  0: 1 3 3 1
                                     0 1 2 3
                (1, 2, 0, -1, total: 1 3 3 1) => 2
                                  0: 1 2 1 .
                                  1: . 1 2 1
                                    0 1 2 3
                (1, 4, 1, 0, total: 1 3 3 1) => 1
                                 0: 1 1 . .
                                 1: . 2 2 .
                                 2: . . 1 1
    o16 : Tally
  Text
    The canonical divisor decomposes into four (-1)-lines and two (-1)-conics, and an elliptic
    curve of class (2,2) on a P1xP1. So the minimal model has K^2_min=0,
    hence is an elliptic surface.

  CannedExample
    i17 :     E=(select(cK,c->genus c ==1))_0;

    o17 : Ideal of P4
    i18 :     betti E,

                  0 1
    o18 = (total: 1 3, )
               0: 1 1
               1: . 2
    o18 : Sequence
    i19 :     saturate ideal singularLocus(P4/E)

    o19 = ideal 1
    o19 : Ideal of P4
    i20 :     dim E,degree E, genus E, minimalBetti E

                           0 1 2 3
    o20 = (2, 4, 1, total: 1 3 3 1)
                        0: 1 1 . .
                        1: . 2 2 .
                        2: . . 1 1
    o20 : Sequence
    i21 :     m=2

    o21 = 2
    i22 :     mE= saturate(E^m+X);

    o22 : Ideal of P4
    i23 :     betti mE

                 0 1
    o23 = total: 1 7
              0: 1 .
              1: . 1
              2: . 6
    o23 : BettiTally
    i24 :     H=ideal( gens mE*random(source gens mE,P4^{-6}));

    o24 : Ideal of P4

    i25 :     linked=saturate((H+X):mE);
        
    o25 : Ideal of P4

    i26 : betti linked, betti saturate linked
                  0  1         0  1
    o26 = (total: 1 15, total: 1 15)
               0: 1  .      0: 1  .
               1: .  .      1: .  .
               2: .  .      2: .  .
               3: .  .      3: .  .
               4: .  4      4: .  4
               5: . 10      5: . 10
               6: .  .      6: .  .
               7: .  1      7: .  1
    o26 : Sequence
    i27 :  H'=ideal(gens linked*random(source gens linked,P4^{-6}));

    o27 : Ideal of P4
    i28 :  betti trim ideal(gens linked%X)
   
                 0 1
    o28 = total: 1 3
              0: 1 .
              1: . .
              2: . .
              3: . .
              4: . .
              5: . 2
              6: . .
              7: . 1
    o28 : BettiTally
    i29 :  betti linked, betti X

                  0  1         0  1
    o29 = (total: 1 15, total: 1 12)
               0: 1  .      0: 1  .
               1: .  .      1: .  .
               2: .  .      2: .  .
               3: .  .      3: .  .
               4: .  4      4: .  4
               5: . 10      5: .  8
               6: .  .
               7: .  1
    o29 : Sequence
    i30 :     E'=(X+H'):linked;

    o30 : Ideal of P4
    i31 :     betti E'

                 0  1
    o31 = total: 1 12
              0: 1  .
              1: .  .
              2: .  8
              3: .  4
    o31 : BettiTally
    i32 :     degree E', genus E'

    o32 = (8, 1)
    o32 : Sequence
    i33 :     dim(E'+E)

    o33 = 0
  Text
    The divisor 2E moves in a pencil.
References
   \textit{Abo, H., Ranestad, K., Schreyer, F-O.} Non-general type surfaces in $\Pn 4$, an update, preprint (2026)
    
SeeAlso
   residualInQuintics
   
   
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
References
   \textit{Bordiga, G.} La superficie del 6d ordine, con 10 rette, nello spazio P4; e le sue proiezioni nello spazio ordinario, Mem. Atti. Accad. Naz. Lincei., 4, (1887), 182-203

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
  of the del Pezzo surface in P4
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
  of the castelnuovo surface in P4
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
    There are 7 singular fibers,
    which fits with Ksquare=1==8-7
///

-* for CannedExample in okonekSurfaceD8S6
Example
    kk=ZZ/nextPrime 10^3;
    P4=kk[x_0..x_4];
    E=kk[e_0..e_4,SkewCommutative=>true];
    minimalBetti(X=okonekSurfaceD8S6(P4,E))
    degree X, sectionalGenus X
    betti(T=tateResolutionOfSurface X)
    betti T.dd_3
    ci=ideal(gens X*random(source gens X,P4^{-3,-4}));
    Y=ci:X;
    minimalBetti Y
    P2=kk[y_0..y_2];
    minimalBetti veroneseSurface(P4,P2)

*-

doc ///
Key
 okonekSurfaceD8S6
 (okonekSurfaceD8S6, PolynomialRing, Ring)
Headline
 construct a degree 8 Okonek surface, sectional genus 6
Usage
 X=okonekSurfaceD8S6(P4,E)
Inputs
 P4:PolynomialRing
  coordinate ring of P4
Outputs
 X:Ideal
  of a degree 8 surface
Description
  Text
    We construct the surface from a randomly choosen differential T.dd_3
    of the Tate resolution of the desired ideal.
  CannedExample
    i1 : kk=ZZ/nextPrime 10^3;
    i2 : P4=kk[x_0..x_4];
    i3 : E=kk[e_0..e_4,SkewCommutative=>true];
    i4 : minimalBetti(X=okonekSurfaceD8S6(P4,E))

                0 1 2 3
    o4 = total: 1 5 5 1
             0: 1 . . .
	     1: . . . .
	     2: . 1 . .
	     3: . 4 5 1

    o4 : BettiTally
    i5 : degree X, sectionalGenus X

    o5 = (8, 6)

    o5 : Sequence
    i6 : betti(T=tateResolutionOfSurface X)

                -1  0  1 2 3 4  5  6   7
    o6 = total: 70 40 19 6 2 9 30 71 140
            -4:  1  .  . . . .  .  .   .
	    -3: 69 40 19 6 . .  .  .   .
	    -2:  .  .  . . 1 .  .  .   .
	    -1:  .  .  . . . .  .  .   .
	     0:  .  .  . . 1 9 30 71 140

    o6 : BettiTally
    i7 : betti T.dd_3

                0 1
    o7 = total: 6 2
            -1: 6 .
	    0: . 1
	    1: . .
	    2: . 1

    o7 : BettiTally
    i8 : ci=ideal(gens X*random(source gens X,P4^{-3,-4}));

    o8 : Ideal of P4
    i9 : Y=ci:X;

    o9 : Ideal of P4
    i10 : minimalBetti Y

                 0 1  2 3 4
    o10 = total: 1 7 10 5 1
              0: 1 .  . . .
	      1: . .  . . .
	      2: . 7 10 5 1

    o10 : BettiTally
    i11 : P2=kk[y_0..y_2];
    i12 : minimalBetti veroneseSurface(P4,P2)

                 0 1  2 3 4
    o12 = total: 1 7 10 5 1
              0: 1 .  . . .
	      1: . .  . . .
	      2: . 7 10 5 1

    o12 : BettiTally  
  Text
    X is linked (3,3) to a Veronese surface.  
References
   \textit{Ionescu, P.} Embedded projective varieties of small invariants III, Proceedings of the l'Aquila conference. LNM., 1417, (1990), 138-154
   \textit{Okonek, Ch.} Fl\"achen vom Grad 8 in $\Pn 4$, Math. Z., 191, (1986), 207-223

     
///

doc ///
Key
 ionescuOkonekSurfaceD7
 (ionescuOkonekSurfaceD7, PolynomialRing,PolynomialRing)
Headline
 construct a Ionescu-Okonek surface of degree 7 and sectional genus 4
Usage
 X= ionescuOkonekSurfaceD7(P4,P2)
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
    X=P2(6;2^6,1^5);
  Example
    kk=ZZ/nextPrime 10^3;
    P4=kk[x_0..x_4];
    P2=kk[y_0..y_2];
    minimalBetti(X=ionescuOkonekSurfaceD7(P4,P2))
    degree X, sectionalGenus X
    elapsedTime (numList,L1,L2,Y)=adjunctionProcess(X,2);
    numList
  Text
    X is rational, the second adjoint is a Del Pezzo surface of degree 3.
References
   \textit{Ionescu, P.} Embedded projective varieties of small invariants III, Proceedings of the l'Aquila conference. LNM., 1417, (1990), 138-154
   \textit{Okonek, Ch.} \"Uber $2$-codimensionale Untermannigfaltigkeiten vom Grad $7$ in $\Pn 4$ und $\Pn 5$, Math. Z., 187, (1983), 209-219
///
///
apply((toList(-4..8),m->chiI(m,8,5,1)))
m2x2=random(E^{2:2},E^{2:1})
betti (T=res coker m2x2)
///

doc ///
Key
 ionescuOkonekSurfaceD8S5
 (ionescuOkonekSurfaceD8S5, PolynomialRing,PolynomialRing)
Headline
 construct a Ionescu-Okonek surface of degree 8 and sectional genus 5
Usage
 X= ionescuOkonekSurfaceD8S5(P4,P2)
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
    We construct a Ionescu-Okonek surface from its rational parametrization:
    X=P2(7;2^10,1); 
  Example
    kk=ZZ/nextPrime 10^3;
    P4=kk[x_0..x_4];
    P2=kk[y_0..y_2];
    minimalBetti(X=ionescuOkonekSurfaceD8S5(P4,P2))
    degree X, sectionalGenus X
    elapsedTime (numList,L1,L2,Y)=adjunctionProcess(X,2);
    numList
  Text
    X is rational, the second adjoint is P2 
References
   \textit{Ionescu, P.} Embedded projective varieties of small invariants III, Proceedings of the l'Aquila conference. LNM., 1417, (1990), 138-154
   \textit{Okonek, Ch.} Fl\"achen vom Grad 8 in $\Pn 4$, Math. Z., 191, (1986), 207-223
///

///
    kk=ZZ/nextPrime 10^3;
    P4=kk[x_0..x_4];
    P2=kk[y_0..y_2];
    minimalBetti(X=ionescuOkonekSurfaceD8S5(P4,P2))
    degree X, sectionalGenus X
    X4=ideal (gens X)_{0..4};
    minimalBetti X4
    Y=X4:X;
    degree Y, sectionalGenus Y
    elapsedTime singX=singularLocus(P4/X);
    dim singX
    dim(X+Y)
    apply(decompose(X+Y),c->(dim c, degree c, genus c, minimalBetti c))
    betti tateResolutionOfSurface X
///
-* For CannedExample of degree10DESSurface
 Example
    kk=ZZ/nextPrime 10^3;
    P4=kk[x_0..x_4];
    E=kk[e_0..e_4,SkewCommutative=>true];
    minimalBetti(X=degree10DESSurface(P4,E))
    degree X, sectionalGenus X
    betti(T=tateResolutionOfSurface X)
    betti(T.dd_4)
    elapsedTime (numList,L1,L2,Y)=adjunctionProcess(X,2);
    numList
*-

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
    of the Tate resolution of the desired ideal. It has degree 10, sectional genus 9 and q=pg=0.
  CannedExample
    i2 :     kk=ZZ/nextPrime 10^3;
    i3 :     P4=kk[x_0..x_4];
    i4 :     E=kk[e_0..e_4,SkewCommutative=>true];
    i5 :     minimalBetti(X=degree10DESSurface(P4,E))

                0  1  2  3 4
    o5 = total: 1 11 18 10 2
             0: 1  .  .  . .
             1: .  .  .  . .
             2: .  .  .  . .
             3: .  1  .  . .
             4: . 10 18 10 2
    o5 : BettiTally
    i6 :     degree X, sectionalGenus X

    o6 = (10, 9)
    o6 : Sequence
    i7 :     betti(T=tateResolutionOfSurface X)

                -1  0  1 2 3 4  5  6   7
    o7 = total: 94 55 27 9 2 3 15 47 105
            -4:  1  .  . . . .  .  .   .
            -3: 93 55 27 9 . .  .  .   .
            -2:  .  .  . . 2 .  .  .   .
            -1:  .  .  . . . 2  .  .   .
             0:  .  .  . . . 1 15 47 105
    o7 : BettiTally
    i8 :     betti(T.dd_4)

                0 1
    o8 = total: 2 3
             1: 2 .
             2: . 2
             3: . 1
    o8 : BettiTally
    i9 :     elapsedTime (numList,L1,L2,Y)=adjunctionProcess(X,2);
       -- 2.34521s elapsed
    i10 :     numList

    o10 = {(4, 10, 9), 7, (8, 13, 6), 7, (5, 5, 1)}
    o10 : List
  Text
    X is a rational surface, the second adjoint is a Del Pezzo surface of degree 5
References
   \textit{Decker, W., Ein, L., Schreyer, F-O.} Construction of surfaces in {${\bf P}\sb 4$}, MJ. Algebraic Geom. 2, (1993), 185--237 
///
-*for CannedExample of degree10pi8RanestadSurface
  Example
    kk=ZZ/nextPrime 10^3;
    P4=kk[x_0..x_4];
    minimalBetti(X=degree10pi8RanestadSurface P4)
    betti(T=tateResolutionOfSurface X)
    (d,sg)=(degree X, sectionalGenus X)
    LeBarzN6(d,sg,1)==6
    Ksquare(d,sg,1)==-4
    residual=residualInQuintics X;
    dim residual, degree residual, betti residual
    tally apply(primaryDecomposition residual,c->(dim c, degree c, betti c,
	    degree (c+X), betti saturate (c+X),
	    tally apply(primaryDecomposition saturate (c+X),d->(dim d, degree radical d))))

*-

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
  CannedExample
    i2 :     kk=ZZ/nextPrime 10^3;
    i3 :     P4=kk[x_0..x_4];
    i4 :     minimalBetti(X=degree10pi8RanestadSurface P4)

                0  1  2  3 4
    o4 = total: 1 14 24 14 3
             0: 1  .  .  . .
             1: .  .  .  . .
             2: .  .  .  . .
             3: .  .  .  . .
             4: . 10 13  4 .
             5: .  4 11 10 3
    o4 : BettiTally
    i5 :     betti(T=tateResolutionOfSurface X)

                -1  0  1 2 3 4  5  6  7
    o5 = total: 90 52 25 8 3 5 13 41 98
            -4:  1  .  . . . .  .  .  .
            -3: 89 52 25 8 . .  .  .  .
            -2:  .  .  . . 1 .  .  .  .
            -1:  .  .  . . 2 5  3  .  .
             0:  .  .  . . . . 10 41 98
    o5 : BettiTally
    i6 :     (d,sg)=(degree X, sectionalGenus X)

    o6 = (10, 8)
    o6 : Sequence
    i7 :     LeBarzN6(d,sg,1)==6

    o7 = true
    i8 :     Ksquare(d,sg,1)==-4

    o8 = true
    i9 :     residual=residualInQuintics X;

    o9 : Ideal of P4

    i10 :     dim residual, degree residual, betti residual

                        0 1
    o10 = (3, 1, total: 1 6)
                     0: 1 .
                     1: . 6
    o10 : Sequence
    i11 :     tally apply(primaryDecomposition residual,c->(dim c, degree c, betti c,
          	    degree (c+X), betti saturate (c+X),
      	        tally apply(primaryDecomposition saturate (c+X),d->(dim d, degree radical d))))

                              0 1            0 1
    o11 = Tally{(2, 1, total: 1 3, 6, total: 1 4, Tally{(1, 1) => 2}) => 1}
                           0: 1 3         0: 1 3        (1, 2) => 2
                                          1: . .
                                          2: . .
                                          3: . .
                                          4: . .
                                          5: . 1
                              0 1            0 1
                (3, 1, total: 1 2, 4, total: 1 5, Tally{(1, 1) => 3}) => 1
                           0: 1 2         0: 1 2        (2, 4) => 1
                                          1: . .
                                          2: . .
                                          3: . .
                                          4: . .
                                          5: . 3
    o11 : Tally
  Text
   There are four 6-secant lines, three of them are in the plane which which intersects X
   in a plane quartic and three points. Hence there X contains two (-1)-lines.
   The adjunction process gives the data L0={(4, 10, 8), 2, (7, 14, 8), 1, (7, 12, 6), 0, (5, 7, 3)}.
   The last adjoint surface is a conic bundle in P5 with 9 singular fibers.
References
   \textit{Decker, W., Ein, L., Schreyer, F-O.} Construction of surfaces in {${\bf P}\sb 4$}, MJ. Algebraic Geom. 2, (1993), 185--237
   \textit{Ranestad, K} On smooth surfaces of degree ten in the projective fourspace, Thesis, Univ. of Oslo, (1988)
SeeAlso
   enriquesSurfaceOfDegree10
   adjunctionProcessData
///

-* possibly to add to degree10pi8RanestadSurface documentation.
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
    have to lie in special position. They satisfy conditions of expected codimension h^0(H)*h^1(H)=10 in the Hilbert scheme
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
-*
 Example
    kk=ZZ/nextPrime 10^3;
    P4=kk[x_0..x_4];
    minimalBetti(X=enriquesSurfaceOfDegree10 P4)
    betti(T=tateResolutionOfSurface X)
    (d,sg)=(degree X, sectionalGenus X)
    LeBarzN6(d,sg,1)==6
    Ksquare(d,sg,1)==-4
    HdotK(d,sg)==4
    R=residualInQuintics X;
    dim R,degree R
    elapsedTime (numList,L1,L2,Y)=adjunctionProcess(X,1);
    numList
    minimalBetti Y
    2*sectionalGenus Y- 2== degree Y
    fourPoints=saturate L2_0;
    dim fourPoints,degree fourPoints
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
  CannedExample
    i2 :     kk=ZZ/nextPrime 10^3;
    i3 :     P4=kk[x_0..x_4];
    i4 :     minimalBetti(X=enriquesSurfaceOfDegree10 P4)

                0  1  2  3 4
    o4 = total: 1 12 21 13 3
             0: 1  .  .  . .
             1: .  .  .  . .
             2: .  .  .  . .
             3: .  .  .  . .
             4: . 10 11  3 .
             5: .  2 10 10 3
    o4 : BettiTally
    i5 :     betti(T=tateResolutionOfSurface X)

                -1  0  1 2 3 4  5  6  7
    o5 = total: 90 52 25 8 3 5 13 41 98
            -4:  1  .  . . . .  .  .  .
            -3: 89 52 25 8 . .  .  .  .
            -2:  .  .  . . 1 .  .  .  .
            -1:  .  .  . . 2 5  3  .  .
             0:  .  .  . . . . 10 41 98
    o5 : BettiTally
    i6 :     (d,sg)=(degree X, sectionalGenus X)

    o6 = (10, 8)
    o6 : Sequence
    i7 :     LeBarzN6(d,sg,1)==6

    o7 = true
    i8 :     Ksquare(d,sg,1)==-4

    o8 = true
    i9 :     HdotK(d,sg)==4

    o9 = true
    i10 :     R=residualInQuintics X;

    o10 : Ideal of P4
    i11 :     dim R,degree R

    o11 = (2, 2)
    o11 : Sequence
    i12 :     elapsedTime (numList,L1,L2,Y)=adjunctionProcess(X,1);
      -- 32.723s elapsed
    i13 :     numList

    o13 = {(4, 10, 8), 4, (7, 14, 8)}
    o13 : List
    i14 :     minimalBetti Y

                 0  1  2  3  4 5
    o14 = total: 1 12 40 56 35 8
              0: 1  .  .  .  . .
              1: .  7  5  .  . .
              2: .  5 35 56 35 8
    o14 : BettiTally
    i15 :     2*sectionalGenus Y- 2== degree Y

    o15 = true
    i16 :     fourPoints=saturate L2_0;

    o16 : Ideal of kk[a ..a ]
                       0   7
    i17 :     dim fourPoints,degree fourPoints

    o17 = (1, 4)
    o17 : Sequence
  Text
    The first adjunction maps blows down 4 (-1) lines. Hence the self-intersection number of the
    canonical divisor on Y is K_Y^2=K_X^2+4=0. Moreover H_Y.K_Y=0. So K_Y is numerically
    trivial and Y is a minimal Enriques surface.
References
   \textit{Brivio,S.}, Smooth Enriques surfaces in $\Pn 4$ and exceptional bundles, Math. Z., 213, (1993), 509-521
   \textit{Decker, W., Ein, L., Schreyer, F-O.}, Construction of surfaces in $\Pn 4$, J. Algebraic Geom., 2,  (1993), 185-237
SeeAlso
    degree10pi8RanestadSurface
    adjunctionProcessData
///

/// -- experiments about the adjoint surface Y=X_1 of the Enriques surface.
kk=ZZ/nextPrime 10^3;
P4=kk[x_0..x_4];
elapsedTime tally apply(5,c->(
	X=enriquesSurfaceOfDegree10 P4;
	elapsedTime (numList,L1,L2,Y)=adjunctionProcess(X,1);
	minimalBetti Y))
-*
                    0  1  2  3  4 5
o142 = Tally{total: 1 12 40 56 35 8 => 5}
                 0: 1  .  .  .  . .
                 1: .  7  5  .  . .
                 2: .  5 35 56 35 8
*-

elapsedTime tally apply(5,c->(
	X=enriquesSurfaceOfDegree10 P4;
	elapsedTime (numList,L1,L2,Y)=adjunctionProcess(X,2);
	(numList,minimalBetti Y)))
-*
 -- 101.272s elapsed

                                                                 0  1  2  3  4 5
o144 = Tally{({(4, 10, 8), 4, (7, 14, 8), 0, (7, 14, 8)}, total: 1 11 39 56 35 8) => 5}
                                                              0: 1  .  .  .  . .
                                                              1: .  7  4  .  . .
                                                              2: .  4 35 56 35 8
*-
elapsedTime tally apply(2,c->(
	X=enriquesSurfaceOfDegree10 P4;
	elapsedTime (numList,L1,L2,Y)=adjunctionProcess(X,1);
	(minimalBetti Y,minimalBetti ideal (gens Y)_{0..6}))
    )
-*
o145 = Tally{(total: 1 12 40 56 35 8, total: 1 7 16 16 7 1) => 2}
                  0: 1  .  .  .  . .      0: 1 .  .  . . .
                  1: .  7  5  .  . .      1: . 7  5  . . .
                  2: .  5 35 56 35 8      2: . . 11 11 . .
                                          3: . .  .  5 7 .
                                          4: . .  .  . . 1
*-
--elapsedTime tally apply(2,c->(
	X=enriquesSurfaceOfDegree10 P4;
	elapsedTime (numList,L1,L2,Y)=adjunctionProcess(X,1);
	J=ideal (gens Y)_{0..6};
	fourPoints=saturate L2_0;
	degree fourPoints, dim fourPoints, minimalBetti fourPoints
	apply(decompose fourPoints,c->(dim c, degree c)) 
	minimalBetti J, minimalBetti Y
	codim Y
	(dim J, degree J), (dim Y, degree Y, genera Y)
	residual=J:Y;
	--cJ=primaryDecomposition J;
	degree residual, dim residual, betti residual
	cResidual=primaryDecomposition residual;
	#cResidual
	netList apply(cResidual,c->(cY=primaryDecomposition saturate(c+Y);(dim c, degree c, betti c,
		dim(c+Y),degree (c+Y), betti saturate (c+Y),genus radical (c+Y),
		tally apply(cY,d->(dim d, degree d, genus d,betti d))
		)))
	tally apply(cResidual,c->(dim(c+fourPoints),
		degree(c+fourPoints),saturate(c+fourPoints)))
	M5x5=matrix apply(cResidual_{0,2,1,4,3},c-> apply(cResidual_{0,2,1,4,3},d->
		if dim(c+d+Y)==1 then degree(c+d+Y) else 0))
	det M4x4
	apply(cResidual_{0..2,4},c->selfIntersectionNumber(Y,c+Y))

	q=cResidual_3_4
	dim ideal jacobian q
	codim cResidual_3, dim cResidual_3, dim (cResidual_3+Y)
	support q, support cResidual_3
	(minimalBetti Y,minimalBetti ideal (gens Y)_{0..6})
    )

--elapsedTime tally apply(2,c->(
	X=enriquesSurfaceOfDegree10 P4;
	elapsedTime (numList,L1,L2,Y)=adjunctionProcess(X,2);
	J=ideal (gens Y)_{0..6};
	minimalBetti J, minimalBetti Y
	codim Y
	(dim J, degree J), (dim Y, degree Y)
	residual=J:Y;
	--cJ=primaryDecomposition J;
	degree residual, dim residual, betti residual
	cResidual=primaryDecomposition residual;
	tally apply(cResidual,c->(cY=primaryDecomposition saturate(c+Y);(dim c, degree c, betti c,
		dim(c+Y),degree (c+Y), betti saturate (c+Y),genus radical (c+Y),
		tally apply(cY,d->(dim d, degree d, genus d,betti d))
		)))
	M4x4=matrix apply(cResidual,c-> apply(cResidual,d->
		if dim(c+d+Y)==1 then degree(c+d+Y) else 0))
	det M4x4
	apply(cResidual,c->selfIntersectionNumber(Y,c+Y))

	q=cResidual_3_4
	dim ideal jacobian q
	codim cResidual_3, dim cResidual_3, dim (cResidual_3+Y)
	support q, support cResidual_3
	(minimalBetti Y,minimalBetti ideal (gens Y)_{0..6}))
    )


///

/// -* surface of degree 10 sectional genus 8 and xO=1 in the intersection of the two components *-
kk=ZZ/nextPrime 10^4
P4=kk[x_0..x_4]
m2x5=transpose matrix apply(5,i->{x_i,(2*i+1) *x_i})
m2x2=matrix{{0,0},{sum(2,i->random kk*x_i^2),sum(toList(2..4),i->random kk*x_i^2)}}
betti(m2x7=map(P4^{2:-2},,m2x5|m2x2))
fm2x7=res coker m2x7
betti fm2x7
fm2x7.dd_3_{0..13}^{0..14}
fm2x7.dd_4_{0..3}^{0..13}
fm2x7.dd_2_{0..14}
betti (s1=syz fm2x7.dd_2_{1..14})
betti syz s1
betti (s2=syz(transpose (s1*random(source s1,P4^{-6})),DegreeLimit=>0))
betti (s3=syz (transpose s2_{0..8}))
betti(s4=syz transpose (fm2x7.dd_2_{1..14}*s3))
betti (X0=trim ideal (transpose s4_{2}*fm2x7.dd_2))
minimalBetti X0
(degree X0, sectionalGenus X0)==(10,8)
betti tateResolutionOfSurface X0
elapsedTime cX0=primaryDecomposition X0;#cX0==1
betti(C=saturate(X0+minors(codim X0,jacobian X0)))
dim C,degree C
cC=primaryDecomposition C;
netList apply(cC,c->(dim c, degree c , betti c, degree radical c))
cC_0, cC_1
matrix apply(cC,c->apply(cC,d->if dim(c+d)==1 then degree radical (c+d) else 0))
-- => X0 has two A1 lines which intersect in the point
radical cC_2

--
radical cC_3, radical cC_4
-- each of the lines contains two pinch points.
-- => in the normalization the lines become conics
twoLines=intersect(cC_0,cC_1)
--
betti(hom=Hom(C/X0,P4^1/X0))
A=prune image homomorphism hom_{1}
-- => the normalization has sectional genus 6, H1 the hyperplane class
radical cC_2
Xaff=sub(X0,x_2=>1);
p=radical(cC_2)
modP2=trim ideal(gens Xaff%p^2)

perhapsTangentCone=(modP3=trim ideal(gens Xaff%p^3))
codim modP3, dim modP3
codim perhapsTangentCone
singPTC=trim (minors(2,jacobian perhapsTangentCone)+perhapsTangentCone)
primaryDecomposition modP3
cSingPTC=primaryDecomposition singPTC;
netList apply(cSingPTC,c->(dim c, degree c, betti c))
-- => presumably it is not the tangent cone

-- guess: the two conics intersect in the normalization in a point.
cPlaneCapX0=primaryDecomposition saturate (X0+ideal(x_1,x_0))
netList apply(cPlaneCapX0,c->(dim c, degree c ,degree radical c, radical c))
dim singularLocus cPlaneCapX0_2
-- => cPlaneCapX0_2 is a smooth conic

-- try to compute a normalization
c0=primaryDecomposition (ideal(x_0+x_1)+X0)
apply(c0,c->(dim c, degree c,degree radical c))
betti (R=intersect(c0_{2,3}))
R
a=R_0,b=R_1
betti(m=matrix{{b^3,a^9}}|gens X0)
betti(sm=syz m)--,DegreeLimit=>12))
sub(sm,matrix{{0_P4,0,0,0,0}})

-- for write up
binomial(9+2,2)-6-14*3-5*1
3^14, 3^8
///

-*
  Example
    kk=ZZ/3;
    P4=kk[x_0..x_4];
    elapsedTime minimalBetti(X=enriquesSurfaceD11S10(P4))
    betti(T=tateResolutionOfSurface X)
    (d,sg)=(degree X, sectionalGenus X)
    LeBarzN6(d,sg,1)==10
    Ksquare(d,sg,1)==-6
    X5=ideal (gens X)_{0..4};
    R=X5:X;
    dim R,degree R,degree(R+X)

 Example
    elapsedTime (numList,L1,L2,Y)=adjunctionProcess(X,4);
    -- 48.7283s elapsed;
    numList=={(4, 11, 10), 5, (9, 19, 11), 1, (10, 20, 11), 0, (10, 20, 11), 0, (10, 20, 11)}
    B=new BettiTally from {(0,{0},0) => 1, (1,{2},2) => 25, (2,{3},3) => 80,
      (2,{4},4) => 10, (3,{4},4) => 80, (3,{5},5) => 112, (4,{6},6) => 350,
      (5,{7},7) => 400, (6,{8},8) => 245, (7,{9},9) => 80, (8,{10},10) => 11}
    degree Y==20
    minimalBetti Y == B
    2*sectionalGenus Y- 2== degree Y
*-

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
    Schreyer surfaces.
  CannedExample
    i2 :     kk=ZZ/3;
    i3 :     P4=kk[x_0..x_4];
    i4 :     elapsedTime minimalBetti(X=enriquesSurfaceD11S10(P4))
         -- 5.08479s elapsed

                0  1  2  3 4
    o4 = total: 1 12 26 20 5
             0: 1  .  .  . .
             1: .  .  .  . .
             2: .  .  .  . .
             3: .  .  .  . .
             4: .  5  .  . .
             5: .  7 26 20 5
    o4 : BettiTally
    i5 :     betti(T=tateResolutionOfSurface X)

                 -1  0  1  2 3 4  5  6  7
    o5 = total: 104 61 30 10 3 5 10 32 84
            -4:   1  .  .  . . .  .  .  .
            -3: 103 61 30 10 . .  .  .  .
            -2:   .  .  .  . 2 .  .  .  .
            -1:   .  .  .  . 1 5  5  .  .
             0:   .  .  .  . . .  5 32 84
    o5 : BettiTally
    i6 :     (d,sg)=(degree X, sectionalGenus X)

    o6 = (11, 10)
    o6 : Sequence
    i7 :     LeBarzN6(d,sg,1)==10

    o7 = true
    i8 :     Ksquare(d,sg,1)==-6

    o8 = true
    i9 :     X5=ideal (gens X)_{0..4};

    o9 : Ideal of P4
    i10 :     R=X5:X;

    o10 : Ideal of P4
    i11 :     dim R,degree R,degree(R+X)

    o11 = (2, 5, 30)
    o11 : Sequence
  Text
    There are 5 six-secant lines, hence by Le Barz formula five (-1) lines. Indeed:
  CannedExample
    i12 :     elapsedTime (numList,L1,L2,Y)=adjunctionProcess(X,4);
      -- 43.1492s elapsed
    i13 :     numList=={(4, 11, 10), 5, (9, 19, 11), 1, (10, 20, 11), 0, (10, 20, 11), 0, (10, 20, 11)}

    o13 = true
    i14 :     B=new BettiTally from {(0,{0},0) => 1, (1,{2},2) => 25, (2,{3},3) => 80,
                (2,{4},4) => 10, (3,{4},4) => 80, (3,{5},5) => 112, (4,{6},6) => 350,
                (5,{7},7) => 400, (6,{8},8) => 245, (7,{9},9) => 80, (8,{10},10) => 11}

                 0  1  2   3   4   5   6  7  8
    o14 = total: 1 25 90 192 350 400 245 80 11
              0: 1  .  .   .   .   .   .  .  .
              1: . 25 80  80   .   .   .  .  .
              2: .  . 10 112 350 400 245 80 11
    o14 : BettiTally
    i15 :     degree Y==20

    o15 = true
    i16 :     minimalBetti Y == B

    o16 = true
    i17 :     2*sectionalGenus Y- 2== degree Y

    o17 = true
  Text
    The first adjunction maps blows down 5 (-1) lines. The second a (-1) conic.
    The second adjoint surface X2 is a minimal Enriques surface of degree 20
    in a P10.
References
   \textit{Decker, W., Ein, L., Schreyer, F-O.}, Construction of surfaces in $\Pn 4$, J. Algebraic Geom., 2,  (1993), 185-237
   \textit{Schreyer, F.-O.}, Small fields in constructive algebraic geometry, in Moduli of Vector bundles, Sanda 1994, Lecture Notes in Pure and Appl. Math., 179, (1996), 221-228 

SeeAlso
    specialEnriquesSchreyerSurface
    specificSchreyerSurface
    adjunctionProcessData
    tateResolutionOfSurface
    LeBarzN6
    Ksquare
///

-* for CannedExample degree10pi9RanestadSurface
  Example
    kk=ZZ/nextPrime 10^3;
    P4=kk[x_0..x_4];
    E=kk[e_0..e_4,SkewCommutative=>true];
    minimalBetti(X=degree10pi9RanestadSurface(P4,E))
    betti(T=tateResolutionOfSurface X)
    betti(T.dd_4)
    degree X, sectionalGenus X
*-

doc ///
Key
 degree10pi9RanestadSurface
 (degree10pi9RanestadSurface, PolynomialRing,Ring)
Headline
 construct a degree 10 sectional genus 9 Ranestad surface
Usage
 X= degree10pi9RanestadSurface(P4,E)
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
    We construct the surface from a carefully chosen differential T.dd_4
    of the Tate resolution.
  CannedExample
    i1 : kk=ZZ/nextPrime 10^3;
    i2 : P4=kk[x_0..x_4];
    i3 : E=kk[e_0..e_4,SkewCommutative=>true];
    i4 : minimalBetti(X=degree10pi9RanestadSurface(P4,E))

                0 1  2 3 4
    o4 = total: 1 8 12 6 1
             0: 1 .  . . .
	     1: . .  . . .
	     2: . .  . . .
	     3: . 2  . . .
	     4: . 5  9 3 .
	     5: . 1  3 3 1

    o4 : BettiTally
    i5 : betti(T=tateResolutionOfSurface X)

                -1  0  1 2 3 4  5  6   7
    o5 = total: 94 55 27 9 2 4 16 47 105
            -4:  1  .  . . . .  .  .   .
            -3: 93 55 27 9 . .  .  .   .
            -2:  .  .  . . 2 .  .  .   .
	    -1:  .  .  . . . 2  1  .   .
	    0:  .  .  . . . 2 15 47 105

    o5 : BettiTally
    i6 : betti(T.dd_4)

                0 1
    o6 = total: 2 4
             1: 2 .
             2: . 2
             3: . 2

    o6 : BettiTally
    i7 : degree X, sectionalGenus X

    o7 = (10, 9)

    o7 : Sequence
  
References
   \textit{Ranestad, K} On smooth surfaces of degree ten in the projective fourspace, Thesis, Univ. of Oslo, (1988)
///
-*
 Example
    kk=ZZ/nextPrime 10^3;
    P4=kk[x_0..x_4];
    elapsedTime minimalBetti(X=nonspecialAlexanderSurface(P4))
    elapsedTime (L0,adjList,ptsList, J)=adjunctionProcess X;
    betti(T=tateResolutionOfSurface X)
 Example 
    LeBarzN6(degree X, sectionalGenus X,1)
    X5=ideal (gens X)_{0..14};
    L=X5:X -- L is the six secant line
    degree(L+X)==6
 Example 
   elapsedTime (L0,adjList,ptsList,J)=adjunctionProcess(X);
    ring J
    betti(H=parametrization(ring J,adjList))
    cH=primaryDecomposition ideal H;
    tally apply(cH,c->(dim c, degree radical c, degree c))
  Example
    P2=kk[y_0..y_2];
    elapsedTime minimalBetti(X=nonspecialAlexanderSurface(P4,P2))
    (L0,adjList,ptsList,J)=adjunctionProcess(X);
    betti(H=parametrization(ring J,adjList))
    cH=primaryDecomposition ideal H;
    tally apply(cH,c->(dim c, degree radical c, degree c))
*-

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
  CannedExample
    i2 :     kk=ZZ/nextPrime 10^3;
    i3 :     P4=kk[x_0..x_4];
    i4 :     elapsedTime minimalBetti(X=nonspecialAlexanderSurface(P4))
     -- .051949s elapsed

                0  1  2  3 4
    o4 = total: 1 16 29 18 4
             0: 1  .  .  . .
             1: .  .  .  . .
             2: .  .  .  . .
             3: .  .  .  . .
             4: . 15 26 15 3
             5: .  1  3  3 1
    o4 : BettiTally
    i5 :     elapsedTime (L0,adjList,ptsList, J)=adjunctionProcess X;
    i6 :     betti(T=tateResolutionOfSurface X)
     -- 1.08535s elapsed

                -1  0  1 2 3 4  5  6   7
    o6 = total: 76 43 20 6 3 5 16 50 112
            -4:  1  .  . . . .  .  .   .
            -3: 75 43 20 6 . .  .  .   .
            -2:  .  .  . . . .  .  .   .
            -1:  .  .  . . 3 5  1  .   .
             0:  .  .  . . . . 15 50 112
    o6 : BettiTally
  Text
    LeBarz formula computes the number of 6-secant lines + the number of (-1) lines.
  CannedExample
    i7 :     LeBarzN6(degree X, sectionalGenus X,1)

    o7 = 1
    i8 :     X5=ideal (gens X)_{0..14};

    o8 : Ideal of P4
    i9 :     L=X5:X -- L is the six secant line

    o9 = ideal (x , x , x )
                 2   1   0
    o9 : Ideal of P4
    i10 :     degree(L+X)==6

    o10 = true
  Text
    We can obtain information about this surface
    from the adjunctionProcess.
  CannedExample
    i11 :    elapsedTime (L0,adjList,ptsList,J)=adjunctionProcess(X);
     -- 1.12776s elapsed
    i12 :     ring J

    o12 = kk[b ..b ]
              0   2
    o12 : PolynomialRing
    i13 :     betti(H=parametrization(ring J,adjList))

                 0 1
    o13 = total: 1 5
              0: 1 .
              1: . .
              2: . .
              3: . .
              4: . .
              5: . .
              6: . .
              7: . .
              8: . .
              9: . .
             10: . .
             11: . .
             12: . 5
    o13 : BettiTally
    i14 :     cH=primaryDecomposition ideal H;
    i15 :     tally apply(cH,c->(dim c, degree radical c, degree c))

    o15 = Tally{(0, 1, 916) => 1}
                (1, 1, 10) => 1
                (1, 4, 40) => 1
                (1, 5, 50) => 1
    o15 : Tally
  Text
    H is a linear system of forms of degree which vanish in 10 points with
    multiplicity 4. However over the field the 10 point split into orbits
    under the Frobenius.
    In the second version of the function we start with
    a rational P2 - -> P4 defined by forms
    of degree 13 which vanishes on 10 randomly choosen
    points with multiplicity 4.
  CannedExample
    i16 :     P2=kk[y_0..y_2];
    i17 :     elapsedTime minimalBetti(X=nonspecialAlexanderSurface(P4,P2))
     -- 5.86527s elapsed

                 0  1  2  3 4
    o17 = total: 1 16 29 18 4
              0: 1  .  .  . .
              1: .  .  .  . .
              2: .  .  .  . .
              3: .  .  .  . .
              4: . 15 26 15 3
              5: .  1  3  3 1
    o17 : BettiTally
    i18 :     (L0,adjList,ptsList,J)=adjunctionProcess(X);
    i19 :     betti(H=parametrization(ring J,adjList))

                 0 1
    o19 = total: 1 5
              0: 1 .
              1: . .
              2: . .
              3: . .
              4: . .
              5: . .
              6: . .
              7: . .
              8: . .
              9: . .
             10: . .
             11: . .
             12: . 5
    o19 : BettiTally
    i20 :     cH=primaryDecomposition ideal H;
    i21 :  tally apply(cH,c->(dim c, degree radical c, degree c))

    o21 = Tally{(0, 1, 2969) => 1}
                  (1, 1, 10) => 10
    o21 : Tally
  Text
    This times the ideal H decomposes in to 10 points of degree 1 defined ove kk
    and an embedded (y_0..y_2)-primary ideal.
References
   \textit{Alexander, J.}, Surfaces rationelles non-speciales dans $\Pn 4 $, Math. Z., 200, (1988), 87-110
   \textit{Decker, W., Ein, L., Schreyer, F-O.}, Construction of surfaces in $\Pn 4$, J. Algebraic Geom., 2,  (1993), 185-237
SeeAlso
   enriquesSurfaceOfDegree9
   tateResolutionOfSurface
   LeBarzN6
   adjunctionProcess
///

-* for CannedExample enriquesSurfaceOfDegree9
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
*-

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
  CannedExample
    i1 : kk=ZZ/nextPrime 10^3;
    i2 : P4=kk[x_0..x_4];
    i3 : elapsedTime minimalBetti(X=enriquesSurfaceOfDegree9(P4))
    -- .0356239s elapsed

                0  1  2  3 4
    o3 = total: 1 15 25 12 1
             0: 1  .  .  . .
	     1: .  .  .  . .
	     2: .  .  .  . .
	     3: .  .  .  . .
	     4: . 15 25 12 .
	     5: .  .  .  . 1

    o3 : BettiTally
    i4 : betti(T=tateResolutionOfSurface X)

    -1  0  1 2 3 4  5  6   7
    o4 = total: 76 43 20 6 3 5 16 50 112
            -4:  1  .  . . . .  .  .   .
	    -3: 75 43 20 6 . .  .  .   .
	    -2:  .  .  . . . .  .  .   .
	    -1:  .  .  . . 3 5  1  .   .
	     0:  .  .  . . . . 15 50 112

    o4 : BettiTally
    i5 : (d,sg)=(degree X, sectionalGenus X)

    o5 = (9, 6)

    o5 : Sequence
    i6 : Ksquare(d,sg,1)==-1

    o6 = true
    i7 : LeBarzN6(d,sg,1)

    o7 = 1
    i8 : elapsedTime (numList,L1,L2,Y)=adjunctionProcess(X,1);
    -- .336708s elapsed
    i9 : numList

    o9 = {(4, 9, 6), 1, (5, 10, 6)}

    o9 : List
    i10 : minimalBetti Y

                 0  1  2 3
    o10 = total: 1 10 15 6
              0: 1  .  . .
	      1: .  .  . .
	      2: . 10 15 6

    o10 : BettiTally
    i11 : 2*sectionalGenus Y -2== degree Y

    o11 = true
    i12 : point=saturate L2_0

    o12 = ideal (a  + 473a , a  + 201a , a  + 287a , a  + 94a , a  + 468a )
                  4       5   3       5   2       5   1      5   0       5

    o12 : Ideal of kk[a ..a ]
                       0   5
    i13 : dim point

    o13 = 1 
  Text
    The self-intersection number of the canonical divisor on the first adjoint surface Y
    is K_Y^2=K_X^2+1=0. Moreover H_Y.K_Y =0. Hence K_Y is numerically trivial
    and Y is a minimal Enriques surface.
References
   \textit {Aure, A., Ranestad, K.}, The Smooth Surfaces of Degree $9$ in $\Pn 4$, LNS,London Math. Soc.,Cambridge Univ. Press, 179,(1992), 32-46
   \textit{Decker, W., Ein, L., Schreyer, F-O.} Construction of surfaces in {$P\sb 4$}, MJ. Algebraic Geom. 2, (1993), 185–237
SeeAlso
   nonspecialAlexanderSurface
   adjunctionProcessData
///


-* for CannedExample in specialityOneAlexanderSurface
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
*-



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
    We construct a speciality one Alexander Surface of degree 9 from its differential
    T.dd_4 of the Tate resolution.
  CannedExample
    i1 : kk=ZZ/nextPrime 10^3;
    i2 : P4=kk[x_0..x_4];
    i3 : E=kk[e_0..e_4,SkewCommutative=>true];
    i4 : elapsedTime minimalBetti(X=specialityOneAlexanderSurface(P4,E))
    -- .177699s elapsed

                0 1  2 3 4
    o4 = total: 1 9 15 9 2
             0: 1 .  . . .
	     1: . .  . . .
	     2: . .  . . .
	     3: . 3  1 . .
	     4: . 6 14 9 2

    o4 : BettiTally
    i5 : degree X, sectionalGenus X

    o5 = (9, 7)

    o5 : Sequence
    i6 : betti(T=tateResolutionOfSurface X)

                -1  0  1 2 3 4  5  6   7
    o6 = total: 80 46 22 7 2 5 20 56 119
            -4:  1  .  . . . .  .  .   .
	    -3: 79 46 22 7 . .  .  .   .
	    -2:  .  .  . . 1 .  .  .   .
	    -1:  .  .  . . 1 2  .  .   .
	     0:  .  .  . . . 3 20 56 119

    o6 : BettiTally
    i7 : betti(T.dd_4)

                0 1
    o7 = total: 2 5
             1: 1 .
	     2: 1 2
	     3: . 3

    o7 : BettiTally
    i8 : betti res(coker random(target T.dd_4,source T.dd_4),LengthLimit=>4)

                0 1  2  3   4
    o8 = total: 2 5 20 56 119
             1: 1 .  .  .   .
             2: 1 2  .  .   .
             3: . 3 20 56 119

    o8 : BettiTally
    i9 : betti res(coker transpose random(target T.dd_4,source T.dd_4),LengthLimit=>5)

                0 1 2  3  4  5
    o9 = total: 5 2 7 22 46 80
            -4: 3 . .  .  .  .
	    -3: 2 1 .  .  .  .
	    -2: . 1 .  .  .  .
	    -1: . . 7 22 46 79
	     0: . . .  .  .  1

    o9 : BettiTally

  Text
    Thus a random choice of the differential T.dd_4 leads to a surface and the component of the Hilbert scheme is unirational.
References
   \textit{Alexander, J.}, Speciality one rational surfaces in $\Pn 4$}, LNS,London Math. Soc., LNS, 179, (1992), 1-23
   \textit{Decker, W., Ein, L., Schreyer, F-O.}, Construction of surfaces in $\Pn 4$, J. Algebraic Geom., 2,  (1993), 185-237
///
-* For CannedExample of popescuSurface
 Example
   kk=ZZ/nextPrime 10^3;
   P4=kk[x_0..x_4];
   E=kk[e_0..e_4,SkewCommutative=>true];
   minimalBetti(X=popescuSurface(P4,E,0))
   (d,sg)=(degree X, sectionalGenus X) 
   betti(T=tateResolutionOfSurface X)
 Example
   elapsedTime minimalBetti(X=popescuSurface(P4,E,1))
   L=residualInQuintics X;
   degree L, degree(L+X)
   elapsedTime (numList,L1,L2,J)=adjunctionProcess(X,1);
   numList_1
 Example
   LeBarzN6(d,sg,1)==6+1
 Example
   elapsedTime minimalBetti(X=popescuSurface(P4,E,2))
   R=residualInQuintics X; 
   tally apply(primaryDecomposition (R+X),c->(dim c,degree radical c,degree(c+R)))

*-

doc ///
Key
 popescuSurface
 (popescuSurface, PolynomialRing,Ring,Number)
Headline
 construct a Popescu surface degree 11 and sectional genus 11 (3 families)
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
  CannedExample
    i2 :    kk=ZZ/nextPrime 10^3;
    i3 :    P4=kk[x_0..x_4];
    i4 :    E=kk[e_0..e_4,SkewCommutative=>true];
    i5 :    minimalBetti(X=popescuSurface(P4,E,0))

                0  1  2 3 4
    o5 = total: 1 10 14 6 1
             0: 1  .  . . .
             1: .  .  . . .
             2: .  .  . . .
             3: .  .  . . .
             4: . 10 12 3 .
             5: .  .  2 3 1
    o5 : BettiTally
    i6 :    (d,sg)=(degree X, sectionalGenus X) 

    o6 = (11, 11)
    o6 : Sequence
    i7 :    betti(T=tateResolutionOfSurface X)

                 -1  0  1  2 3 4  5  6  7
    o7 = total: 108 64 32 11 3 3 11 38 91
            -4:   1  .  .  . . .  .  .  .
            -3: 107 64 32 11 . .  .  .  .
            -2:   .  .  .  . 3 1  .  .  .
            -1:   .  .  .  . . 2  1  .  .
             0:   .  .  .  . . . 10 38 91
    o7 : BettiTally

  Text
   In the second case there is a unique 6-secant line.
  CannedExample
    i8 :    elapsedTime minimalBetti(X=popescuSurface(P4,E,1))
     -- .582183s elapsed

                0  1  2 3 4
    o8 = total: 1 11 16 7 1
             0: 1  .  . . .
             1: .  .  . . .
             2: .  .  . . .
             3: .  .  . . .
             4: . 10 13 4 .
             5: .  1  3 3 1
    o8 : BettiTally
    i9 :    L=residualInQuintics X;

    o9 : Ideal of P4
    i10 :    degree L, degree(L+X)

    o10 = (1, 6)
    o10 : Sequence
    i11 :    elapsedTime (numList,L1,L2,J)=adjunctionProcess(X,1);
     -- 9.37388s elapsed
    i12 :    numList_1

    o12 = 6

  Text
   The entry numList_1 is the number of (-1) lines on X. Thus we must have
  CannedExample
    i13 :    LeBarzN6(d,sg,1)==6+1

    o13 = true
  Text
   In the third case there is a pencil of 6-secant line. Every line in
   the plane through the point is a 6-secant line,
   since the plane intersects the surface in a plane quintic curve.
  CannedExample
    i14 :    elapsedTime minimalBetti(X=popescuSurface(P4,E,2))
     -- .526975s elapsed
 
                 0  1  2  3 4
    o14 = total: 1 12 19 10 2
              0: 1  .  .  . .
              1: .  .  .  . .
              2: .  .  .  . .
              3: .  .  .  . .
              4: . 10 14  6 1
              5: .  2  5  4 1

    o14 : BettiTally
    i15 :    R=residualInQuintics X; 

    o15 : Ideal of P4
    i16 :    tally apply(primaryDecomposition (R+X),c->(dim c,degree radical c,degree(c+R)))

    o16 = Tally{(1, 1, 2) => 1}
                (2, 5, 5) => 1
    o16 : Tally

  Text
   
References
   \textit{Popescu, S.}, Surfaces of degree $\ge 11$ in the Projective Fourspace, Dissertation, Universit\"at des Saarlandes, (1993)
SeeAlso
  adjunctionProcessData
  residualInQuintics

///
-*
 Example
   P4=ZZ/2[x_0..x_4]; P2=ZZ/2[u_0..u_2];
   elapsedTime minimalBetti(X=vBELSurface(P4,P2))
   ci=ideal ((gens X)_{0}|(gens X)*random(source gens X,P4^{-5}));
   Y=ci:X;
   setRandomSeed("fast decomposition")
   elapsedTime cY=decompose Y;
   tally apply(cY, c-> (dim c, degree c, minimalBetti c))
   betti(T=tateResolutionOfSurface X)
  Text
   The linked surface consists of a plane, a quadric surface and a Bordiga surface.
   The unirational construction is a reversal of this linkage.
  Example
   kk=ZZ/nextPrime 10^3; P4=kk[x_0..x_4];
   minimalBetti(X=vBELSurface P4)
   betti tateResolutionOfSurface X
   elapsedTime (L0,L1,L2,J)=adjunctionProcess(X);
   L0
   X45=ideal (gens X)_{0..5};
   R=X45:X;
   dim R, degree R
   cR=decompose R;
   tally apply(cR,c->(dim c, degree c, betti c))
   tally apply(cR,c->degree(c+X))
   LeBarzN6(11,11,1)
*-
doc ///
Key
 vBELSurface
 (vBELSurface, PolynomialRing)
 (vBELSurface, Ring,Ring)
Headline
 construct a von Bothmer-Erdenberger-Ludwig surface, degree 11, sectional genus 11
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
   The first version gives the original vBEL surface defined over a field of characteristic 2.
   The second version gives gives a construction of a vBEL surface building on a unirational liaison
   construction.
  CannedExample
    i2 :    P4=ZZ/2[x_0..x_4]; P2=ZZ/2[u_0..u_2];
    i4 :    elapsedTime minimalBetti(X=vBELSurface(P4,P2))
      -- 1.33181s elapsed

                0 1  2 3 4
    o4 = total: 1 8 13 8 2
             0: 1 .  . . .
             1: . .  . . .
             2: . .  . . .
             3: . 1  . . .
             4: . 5  4 . .
             5: . 2  9 8 2
    o4 : BettiTally
    i5 :    ci=ideal ((gens X)_{0}|(gens X)*random(source gens X,P4^{-5}));

    o5 : Ideal of P4
    i6 :    Y=ci:X;

    o6 : Ideal of P4
    i7 :    setRandomSeed("fast decomposition")
       -- setting random seed to 1219499381431827880741147639187005567

    o7 = 1219499381431827880741147639187005567
    i8 :    elapsedTime cY=decompose Y;
       -- .397658s elapsed
    i9 :    tally apply(cY, c-> (dim c, degree c, minimalBetti c))

                             0 1 2
    o9 = Tally{(3, 1, total: 1 2 1) => 1}
                          0: 1 2 1
                             0 1 2
               (3, 2, total: 1 2 1) => 1
                          0: 1 1 .
                          1: . 1 1
                             0 1 2
               (3, 6, total: 1 4 3) => 1
                          0: 1 . .
                          1: . . .
                          2: . 4 3
    o9 : Tally
    i10 :    betti(T=tateResolutionOfSurface X)

                  -1  0  1  2 3 4  5  6  7
    o10 = total: 108 64 32 11 3 4 12 38 91
             -4:   1  .  .  . . .  .  .  .
             -3: 107 64 32 11 . .  .  .  .
             -2:   .  .  .  . 3 1  .  .  .
             -1:   .  .  .  . . 2  2  .  .
              0:   .  .  .  . . 1 10 38 91
    o10 : BettiTally
 Text
   The linked surface consists of a plane, a quadric surface and a Bordiga surface.
   The unirational construction is a reversal of this linkage.
 CannedExample
    i11 :    kk=ZZ/nextPrime 10^3; P4=kk[x_0..x_4];
    i13 :    minimalBetti(X=vBELSurface P4)

                 0 1  2 3 4
    o13 = total: 1 8 13 8 2
              0: 1 .  . . .
              1: . .  . . .
              2: . .  . . .
              3: . 1  . . .
              4: . 5  4 . .
              5: . 2  9 8 2
    o13 : BettiTally
    i14 :    betti tateResolutionOfSurface X

                  -1  0  1  2 3 4  5  6  7
    o14 = total: 108 64 32 11 3 4 12 38 91
             -4:   1  .  .  . . .  .  .  .
             -3: 107 64 32 11 . .  .  .  .
             -2:   .  .  .  . 3 1  .  .  .
             -1:   .  .  .  . . 2  2  .  .
              0:   .  .  .  . . 1 10 38 91
    o14 : BettiTally
    i15 :    elapsedTime (L0,L1,L2,J)=adjunctionProcess(X);
     -- 13.611s elapsed
    i16 :    L0

    o16 = {(4, 11, 11), 5, (10, 18, 9), 14, (8, 8, 1)}
    o16 : List
    i17 :    X45=ideal (gens X)_{0..5};

    o17 : Ideal of P4
    i18 :    R=X45:X;

    o18 : Ideal of P4
    i19 :    dim R, degree R

    o19 = (2, 2)
    o19 : Sequence
    i20 :    cR=decompose R;
    i21 :    tally apply(cR,c->(dim c, degree c, betti c))

                              0 1
    o21 = Tally{(2, 1, total: 1 3) => 2}
                           0: 1 3
    o21 : Tally
    i22 :    tally apply(cR,c->degree(c+X))

    o22 = Tally{6 => 2}
    o22 : Tally
    i23 :    LeBarzN6(11,11,1)

    o23 = 7

  Text
   X has two 6-secant lines and five (-1)-lines.
References
   \textit{Graf von Bothmer, H-C., Erdenberger, C.,Ludwig, K.}, A new family of rational surfaces in $\Pn 4$, J. Symbolic Comput., 39,  (2005), 51-60
   \textit{Graf von Bothmer, H-C., Ranestad, K.},  Classification of rational surfaces of degree 11 and sectional genus 11 in $\Pn 4$, Math. Scand., 104, (2009), 60-94
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
-* for CannedExample quinticEllipticScroll

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
*-

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
  CannedExample
   i1 : kk=ZZ/nextPrime 10^3;
   i2 : P4=kk[x_0..x_4];
   i3 : X=quinticEllipticScroll P4;

   o3 : Ideal of P4
   i4 : (d,sg)=(degree X, sectionalGenus X)

   o4 = (5, 1)

   o4 : Sequence
   i5 : minimalBetti X

               0 1 2 3
   o5 = total: 1 5 5 1
            0: 1 . . .
	    1: . . . .
	    2: . 5 5 1

   o5 : BettiTally
   i6 : betti(T=tateResolutionOfSurface X)

               -1  0 1 2 3  4  5   6   7
   o6 = total: 31 15 5 1 5 20 51 105 190
           -4:  1  . . . .  .  .   .   .
	   -3: 30 15 5 . .  .  .   .   .
	   -2:  .  . . 1 .  .  .   .   .
	   -1:  .  . . . .  .  .   .   .
	    0:  .  . . . 5 20 51 105 190

   o6 : BettiTally
   i7 : ci=ideal(gens X* random(source gens X,P4^{2:-3}));

   o7 : Ideal of P4
   i8 : Y=ci:X; -- Y is a Veronese surface

   o8 : Ideal of P4
   i9 : minimalBetti Y

               0 1  2 3 4
   o9 = total: 1 7 10 5 1
            0: 1 .  . . .
	    1: . .  . . .
	    2: . 7 10 5 1

   o9 : BettiTally
   i10 : (degree Y, sectionalGenus Y)==(4,0)

   o10 = true

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
   \textit{Abo, H., Decker, W., Sasakura, N.},  An elliptic conic bundle arising from a stable rank-3 vector bundle,  Math. Z., 229, (1998), 725-741
SeeAlso
  tateResolutionOfSurface
///
-* for CannedExample of biellipticSurfaceD10
 Example
   kk=ZZ/nextPrime 10^3;
   P4=kk[x_0..x_4];
   elapsedTime X=biellipticSurfaceD10 P4;
   (d,sg)=(degree X, sectionalGenus X)
   minimalBetti X
   betti(T=tateResolutionOfSurface X)
*-
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
   We construct a bielliptic surface of degree 10 
  CannedExample
    i2 :    kk=ZZ/nextPrime 10^3;
    i3 :    P4=kk[x_0..x_4];
    i4 :    elapsedTime X=biellipticSurfaceD10 P4;
       -- 45.9089s elapsed

    o4 : Ideal of P4
    i5 :    (d,sg)=(degree X, sectionalGenus X)

    o5 = (10, 6)
    o5 : Sequence
    i6 :    minimalBetti X

                0  1  2  3  4
    o6 = total: 1 26 55 40 10
             0: 1  .  .  .  .
             1: .  .  .  .  .
             2: .  .  .  .  .
             3: .  .  .  .  .
             4: .  1  .  .  .
             5: . 25 55 40 10
    o6 : BettiTally
    i7 :    betti(T=tateResolutionOfSurface X)

                -1  0  1 2 3  4  5  6  7
    o7 = total: 81 45 20 6 5 10 11 30 85
            -4:  1  .  . . .  .  .  .  .
            -3: 80 45 20 5 .  .  .  .  .
            -2:  .  .  . 1 .  .  .  .  .
            -1:  .  .  . . 5 10 10  .  .
             0:  .  .  . . .  .  1 30 85
    o7 : BettiTally

 Text
   The construction uses Moore matrices and a search for 6 torsions point on an elliptic curve.
References
   \textit{Serrano, F.}, Divisors on bielliptic surfaces and embeddings in $\Pn 4$, Math. Z., 203, (1990), 527-533
   \textit{Aure, A.,Decker, W., Hulek, K., Popescu, S.,Ranestad, K.  Syzygies of abelian and bielliptic surfaces in. $\Pn 4$, Int. J. of Math., 8, (1997),  849-919
SeeAlso
  tateResolutionOfSurface
///
-* for CannedExample of biellipticSurfaceD15
  Example
   kk=ZZ/nextPrime 10^4; 
   P4=kk[x_0..x_4];
   elapsedTime X=biellipticSurfaceD15 P4;
   (d,sg)=(degree X, sectionalGenus X)
   minimalBetti X
   betti(T=tateResolutionOfSurface X)
*-
doc ///
Key
 biellipticSurfaceD15
 (biellipticSurfaceD15,PolynomialRing)
Headline
 construct a bielliptic surface of degree 15 
Usage
 X=biellipticSurfaceD15 P4
Inputs
 P4:PolynomialRing
  coordinate ring of P4
Outputs
 X:Ideal
  of a bielliptic surface of degree 15 
Description
  Text
    We construct a nonminimal bielliptic surface of degree 15
  CannedExample
     i2 :    kk=ZZ/nextPrime 10^4; 
     i3 :    P4=kk[x_0..x_4];
     i4 :    elapsedTime X=biellipticSurfaceD15 P4;
        -- 11.3729s elapsed

     o4 : Ideal of P4
     i5 : (d,sg)=(degree X, sectionalGenus X)

     o5 = (15, 21)
     o5 : Sequence
     i6 :    minimalBetti X

                 0  1  2 3
     o6 = total: 1 11 15 5
              0: 1  .  . .
              1: .  .  . .
              2: .  .  . .
              3: .  .  . .
              4: .  1  . .
              5: . 10 15 5
     o6 : BettiTally
     i7 :    betti(T=tateResolutionOfSurface X)

                  -1   0  1  2  3  4 5  6  7
     o7 = total: 171 105 55 21 10 10 6 15 50
             -4:   1   .  .  .  .  . .  .  .
             -3: 170 105 55 20  .  . .  .  .
             -2:   .   .  .  1 10 10 5  .  .
             -1:   .   .  .  .  .  . .  .  .
              0:   .   .  .  .  .  . 1 15 50
     o7 : BettiTally
     
 Text
   The construction uses Moore matrices and a search for 6 torsions point on an elliptic curve.
Caveat
   The function can fail, in which case it returns null.
References
   \textit{Aure, A.,Decker, W., Hulek, K., Popescu, S.,Ranestad, K.  Syzygies of abelian and bielliptic surfaces in. $\Pn 4$, Int. J. of Math., 8, (1997),  849-919
SeeAlso
  tateResolutionOfSurface
///

-* for CannedExample in abelianSurfaceD10
  Example
    kk=ZZ/nextPrime 10^4; 
    P4=kk[x_0..x_4];
    X=abelianSurfaceD10 P4;
    betti(fX=res X)
    (d,sg)=(degree X, sectionalGenus X)
    betti(T=tateResolutionOfSurface(X,7))
    k2=Ksquare(10,6,0)
    LeBarzN6(10,6,0)==25
    tally apply(decompose residualInQuintics(X),c->(dim c-1, degree c,
	    (dim(c+X)-1 ,degree(c+X))))
  Text
    X has 25 six-secant lines. It is linked in a (5,5) complete intersection to a surface X' of
    degree 15. The six secant lines are  twentyfive  (-1)-lines of X'.
  Example 
    ci=ideal(gens X*random(source gens X,P4^{2:-5}));
    X'=ci:X;
    minimalBetti X'
    betti tateResolutionOfSurface(X',7)
    (d',sg')=(degree X',sectionalGenus X')
    Ksquare(d',sg',0)==-25
    LeBarzN6(d',sg',0)==LeBarzN6(d,sg,0)
    saturate residualInQuintics(X')
  Text
    The surface X is the zero loci of a vector bundle, whose
    module of global sections is
  Example
    HMBundle=coker transpose (syz transpose fX.dd_3)_{0..18};
    minimalBetti HMBundle
  Text
    In the code we use the Horrocks-Mumford bundle to get X. 
    The construction of the Horrocks-Mumford bundle uses a monad:
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
    F=res( coker alphad,LengthLimit=>7);
    betti (F'=res(coker transpose F.dd_6,LengthLimit=>10)[5]**E^{0})
  Text
    The Horrocks-Bundle is obtained as the homology of a monad. The module HMbundle below
    is the module of global sections of the Horrocks-Mumford bundle.
  Example
    HMbundle= (prune homology(beilinson(F'.dd_0**E^{-4},P4),beilinson(F'.dd_1**E^{-4},P4)))**P4^{-4}
    minimalBetti HMbundle
    minimalBetti X
  Text
    The Hilbert function of the cohomology of the Horrocks-Mumford bundle is incoded in the
    Tate resolution, cf. [EFS,Example 7.1].
  Example
    H2cohomology=prune Ext^2(HMbundle,P4^{-5})
    H1cohomology=prune Ext^1(HMbundle,P4^{-5})
    apply(toList(1..6),i->hilbertFunction(i,H1cohomology))
    betti F'


*-


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
  of an abelian surface of degree 10, a Horrocks-Mumford surface. 
Description
  Text
    Horrocks and Mumford rediscovered these surfaces as the zero locus of sections of the
    Horrocks-Mumford bundle, which is a rank 2 vector bundle with
    Chern classes c1=-1 and c2=4.
    Commesati found these surfaces already in 1919.
  CannedExample
    i1 : kk=ZZ/nextPrime 10^4;
    i2 : P4=kk[x_0..x_4];
    i3 : X=abelianSurfaceD10 P4;

    o3 : Ideal of P4
    i4 : betti(fX=res X)

                0  1  2  3 4
    o4 = total: 1 18 35 20 2
             0: 1  .  .  . .
             1: .  .  .  . .
             2: .  .  .  . .
             3: .  .  .  . .
             4: .  3  .  . .
             5: . 15 35 20 .
             6: .  .  .  . 2

    o4 : BettiTally
    i5 : (d,sg)=(degree X, sectionalGenus X)

    o5 = (10, 6)

    o5 : Sequence
    i6 : betti(T=tateResolutionOfSurface(X,7))

                -1  0  1 2 3  4  5  6  7   8
    o6 = total: 81 45 20 7 6 10 13 32 85 175
            -4:  1  .  . . .  .  .  .  .   .
            -3: 80 45 20 5 1  .  .  .  .   .
            -2:  .  .  . 2 .  .  .  .  .   .
            -1:  .  .  . . 5 10 10  2  .   .
             0:  .  .  . . .  .  3 30 85 175

    o6 : BettiTally
    i7 : k2=Ksquare(10,6,0)

    o7 = 0
    i8 : LeBarzN6(10,6,0)==25

    o8 = true
    i9 : tally apply(decompose residualInQuintics(X),c->(dim c-1, degree c,
             (dim(c+X)-1 ,degree(c+X))))

    o9 = Tally{(1, 1, (0, 6)) => 5 }
               (1, 4, (0, 24)) => 5

    o9 : Tally

  Text
    X has 25 six-secant lines. It is linked in a (5,5) complete intersection to a surface X' of
    degree 15. The six secant lines are  twentyfive  (-1)-lines of X'.
    X has 25 six-secant lines. It is linked in a (5,5) complete intersection to a surface X' of degree 15. The six secant lines are twentyfive (-1)-lines of X'.
  CannedExample
    i10 : ci=ideal(gens X*random(source gens X,P4^{2:-5}));

    o10 : Ideal of P4
    i11 : X'=ci:X;

    o11 : Ideal of P4
    i12 : minimalBetti X'

                 0 1  2  3 4
    o12 = total: 1 8 15 10 2
              0: 1 .  .  . .
              1: . .  .  . .
              2: . .  .  . .
              3: . .  .  . .
              4: . 3  .  . .
              5: . .  .  . .
              6: . 5 15 10 2

    o12 : BettiTally
    i13 : betti tateResolutionOfSurface(X',7)

                  -1   0  1  2  3  4 5  6  7   8
    o13 = total: 171 105 55 22 11 10 8 17 50 115
             -4:   1   .  .  .  .  . .  .  .   .
             -3: 170 105 55 20  1  . .  .  .   .
             -2:   .   .  .  2 10 10 5  .  .   .
             -1:   .   .  .  .  .  . .  2  .   .
              0:   .   .  .  .  .  . 3 15 50 115

    o13 : BettiTally
    i14 : (d',sg')=(degree X',sectionalGenus X')

    o14 = (15, 21)

    o14 : Sequence
    i15 : Ksquare(d',sg',0)==-25

    o15 = true
    i16 : LeBarzN6(d',sg',0)==LeBarzN6(d,sg,0)

    o16 = true
    i17 : saturate residualInQuintics(X')

    o17 = ideal 1

    o17 : Ideal of P4
  Text
    The surface X is the zero loci of a vector bundle, whose
    module of global sections is
  CannedExample
    i18 : HMBundle=coker transpose (syz transpose fX.dd_3)_{0..18};
    i19 : minimalBetti HMBundle

                  0  1  2 3
    o19 = total: 19 35 20 2
               5:  4  .  . .
               6: 15 35 20 .
               7:  .  .  . 2

     o19 : BettiTally
  Text
    In the code we use the Horrocks-Mumford bundle to get X. 
    The construction of the Horrocks-Mumford bundle uses a monad:In the code we use the Horrocks-Mumford bundle to get X. The construction of the Horrocks-Mumford bundle uses a monad:
  CannedExample
    i20 : e=symbol e;
    i21 : E=kk[e_0..e_4,SkewCommutative=>true];
    i22 : alphad= map(E^{5:0},E^{2:-2},{{e_4*e_1,e_2*e_3},{e_0*e_2,e_3*e_4},{e_1*e_3,e_4*e_0},{e_2*e_4,e_0*e_1},{e_3*e_0,e_1*e_2}});

                  5      2
    o22 : Matrix E  <-- E
  Text
    The matrix
  CannedExample
    i23 : diagonalMatrix{1,-1}*transpose alphad
    
    o23 = | e_1e_4 -e_0e_2 -e_1e_3 -e_2e_4 e_0e_3 |
          | e_2e_3 e_3e_4  -e_0e_4 e_0e_1  e_1e_2 |
                  2      5
    o23 : Matrix E  <-- E                 
  Text
    is the famous Horrocks-Mumford matrix which leads to a Tate resolution of the following shape
  CannedExample
    i24 : F=res( coker alphad,LengthLimit=>7);
    i25 : betti (F'=res(coker transpose F.dd_6,LengthLimit=>10)[5]**E^{0})

                  -5 -4 -3 -2 -1 0 1  2  3  4   5
    o25 = total: 100 37 14 10  5 2 5 10 14 37 100
             -4: 100 35  4  .  . . .  .  .  .   .
             -3:   .  2 10 10  5 . .  .  .  .   .
             -2:   .  .  .  .  . 2 .  .  .  .   .
             -1:   .  .  .  .  . . 5 10 10  2   .
              0:   .  .  .  .  . . .  .  4 35 100

    o25 : BettiTally
  Text
    The Horrocks-Bundle is obtained as the homology of a monad. The module HMbundle below
    is the module of global sections of the Horrocks-Mumford bundle.
  CannedExample
    i26 : HMbundle= (prune homology(beilinson(F'.dd_0**E^{-4},P4),beilinson(F'.dd_1**E^{-4},P4)))**P4^{-4}

    o26 = cokernel {7} | -x_1x_4 x_3^2 0     x_1x_3  x_4^2 0      0     x_2x_3  x_1^2 -x_2x_4 x_0^2   x_0x_2  0     0    -x_0x_3 0    0     0    0      0    0      0      x_2^2 0      0    0      0       x_0x_4 x_1x_2 x_0x_1 0      0    0       0      x_3x_4 |
                   {7} | x_2x_3  0     x_4^2 -x_0x_4 0     x_0x_3 x_1^2 0       0     x_0x_1  0       -x_3x_4 x_2^2 0    x_1x_2  0    x_3^2 0    0      0    x_0x_2 x_1x_4 0     0      0    0      -x_2x_4 0      0      0      x_0^2  0    -x_1x_3 0      0      |
                   {7} | 0       0     0     0       0     0      0     0       0     0       -x_1x_4 0       0     0    0       0    0     0    x_2x_4 0    0      x_2x_3 0     x_1x_3 0    0      0       0      x_4^2  0      0      0    0       0      x_1^2  |
                   {7} | 0       0     0     0       0     0      0     -x_1x_4 0     0       0       0       0     0    0       0    0     0    0      0    0      0      0     0      0    x_3x_4 x_3^2   0      0      0      x_2x_3 0    x_2^2   x_1x_2 0      |
                   {8} | -x_0    -x_1  x_3   0       0     0      x_2   0       0     0       0       0       0     0    0       0    0     0    -x_1   0    0      0      -x_4  -x_4   0    -x_2   0       0      0      0      0      0    0       -x_3   0      |
                   {8} | 0       -x_4  0     0       0     -x_1   0     0       0     0       0       0       0     0    0       x_0  0     0    -x_4   0    0      -x_3   0     0      0    0      0       x_2    0      0      0      0    0       0      0      |
                   {8} | 0       0     -x_2  0       0     0      0     -x_4    0     0       0       0       0     0    0       0    0     x_0  0      0    x_1    0      0     0      0    0      0       -x_3   0      0      0      0    0       x_2    0      |
                   {8} | 0       0     0     -x_2    x_1   0      0     0       0     0       0       0       0     0    0       0    0     x_4  0      -x_3 0      0      0     0      x_1  -x_0   0       0      0      0      0      0    0       0      0      |
		   {8} | 0       0     0     0       -x_3  0      0     x_0     -x_2  0       0       0       0     0    0       -x_2 0     0    0      0    0      0      0     0      -x_3 0      x_1     0      0      0      0      0    x_4     0      0      |
		   {8} | 0       0     0     0       0     x_2    0     0       0     0       x_4     0       0     0    0       0    0     0    0      x_4  0      0      0     -x_3   0    0      -x_0    0      0      0      0      0    0       0      -x_1   |
		   {8} | 0       0     0     0       0     x_4    -x_3  -x_1    0     0       0       0       0     x_0  0       0    0     0    0      0    0      0      0     0      0    x_3    0       0      0      -x_2   0      0    0       0      0      |
		   {8} | 0       0     0     0       0     0      0     0       -x_4  -x_3    -x_2    0       0     -x_1 0       -x_4 0     0    0      -x_2 0      0      0     0      0    0      0       0      0      0      0      0    0       x_0    0      |
		   {8} | 0       0     0     0       0     0      0     0       0     0       0       -x_1    -x_3  -x_3 0       0    0     0    -x_0   0    0      0      0     0      -x_2 0      0       0      0      0      -x_4   x_4  0       0      0      |
		   {8} | 0       0     0     0       0     0      0     0       0     0       0       0       -x_4  -x_4 0       0    -x_1  -x_1 0      0    0      x_0    0     0      0    0      0       0      -x_3   0      0      0    0       0      -x_2   |
		   {8} | 0       0     0     0       0     0      0     0       0     0       0       0       0     0    -x_4    x_3  x_2   x_2  0      0    0      0      0     x_0    0    0      0       0      0      0      0      x_1  0       0      0      |
		   {8} | 0       0     0     0       0     0      0     0       0     0       0       0       0     0    0       0    0     0    x_2    x_1  -x_3   0      0     0      0    0      0       0      x_4    0      0      0    x_0     0      0      |
		   {8} | 0       0     0     0       0     0      0     0       0     0       0       0       0     0    0       0    0     0    0      0    -x_4   -x_2   -x_1  -x_1   x_0  0      0       0      0      x_3    0      0    0       0      0      |
		   {8} | 0       0     0     0       0     0      0     0       0     0       0       0       0     0    0       0    0     0    0      0    0      0      0     0      0    -x_4   -x_3    -x_1   -x_0   0      0      -x_2 0       0      0      |
		   {8} | 0       0     0     0       0     0      0     0       0     0       0       0       0     0    0       0    0     0    0      0    0      0      0     0      0    0      0       0      0      -x_4   -x_3   x_3  -x_2    -x_1   -x_0   |

                               19
    o26 : P4-module, quotient of P4
    i27 : minimalBetti HMbundle

                  0  1  2 3
    o27 = total: 19 35 20 2
              7:  4  .  . .
              8: 15 35 20 .
              9:  .  .  . 2

    o27 : BettiTally
    i28 : minimalBetti X

                 0  1  2  3 4
    o28 = total: 1 18 35 20 2
              0: 1  .  .  . .
	      1: .  .  .  . .
	      2: .  .  .  . .
	      3: .  .  .  . .
	      4: .  3  .  . .
	      5: . 15 35 20 .
	      6: .  .  .  . 2

    o28 : BettiTally

  Text
    The Hilbert function of the cohomology of the Horrocks-Mumford bundle is incoded in the
    Tate resolution, cf. [EFS,Example 7.1].
  CannedExample
    i29 : H2cohomology=prune Ext^2(HMbundle,P4^{-5})

    o29 = cokernel {-2} | x_4 x_3 x_2 x_1 x_0 0   0   0   0   0   |
                   {-2} | 0   0   0   0   0   x_4 x_3 x_2 x_1 x_0 |

                                   2
    o29 : P4-module, quotient of P4
    i30 : H1cohomology=prune Ext^1(HMbundle,P4^{-5})

    o30 = cokernel | x_3 x_0  0   0   x_1  0   0   0    0    x_2 0    0    0   x_4 0   |
                   | 0   -x_4 x_1 x_2 0    0   0   0    -x_3 0   0    x_0  0   0   0   |
		   | 0   0    0   x_4 -x_2 x_0 0   x_1  0    0   x_3  0    0   0   0   |
		   | 0   0    0   0   0    0   x_4 -x_3 x_2  x_0 0    0    0   0   x_1 |
		   | 0   0    0   0   0    0   0   0    0    0   -x_4 -x_3 x_2 x_1 x_0 |

		                   5
    o30 : P4-module, quotient of P4
    i31 : apply(toList(1..6),i->hilbertFunction(i,H1cohomology))

    o31 = {10, 10, 2, 0, 0, 0}

    o31 : List
    i32 : betti F'

                  -5 -4 -3 -2 -1 0 1  2  3  4   5
    o32 = total: 100 37 14 10  5 2 5 10 14 37 100
             -4: 100 35  4  .  . . .  .  .  .   .
             -3:   .  2 10 10  5 . .  .  .  .   .
             -2:   .  .  .  .  . 2 .  .  .  .   .
	     -1:   .  .  .  .  . . 5 10 10  2   .
	      0:   .  .  .  .  . . .  .  4 35 100

    o32 : BettiTally

References
   \textit{Horrocks, G., Mumford, D.}, A rank 2 vector bundle on {P}{{\(^4\)}} with 15,000 symmetries, Topology ,212, (1973), 63-81

   \textit{Comessatti, A.}, Sulle superficie di Jacobi simplicimente singolari, Mem. Ital. delle Scienze (dei XL) serie 3a, 21, (1919), 45-71
   
   \textit{Barth, W., Hulek, K., Moore, R.}, Degenerations of {Horrocks}-{Mumford} surfaces, Math. Ann.,277, (1987), 735-755
  
   \textit{Decker, W., Schreyer, F-O.}, On the uniqueness of the {Horrocks}-{Mumford}-bundle, Math. Ann., 273,(1986),415-443

   \textit{Eisenbud, D., Fl\o ystad, G., Schreyer, F-O.}, Sheaf cohomology and free resolutions over exterior algebras ,Trans. Amer. Math. Soc., 355,(2003), 4397-4426

SeeAlso
  searchHMBundle
///
-* for CannedExample abelianSurfaceD15
  Example
   kk=ZZ/nextPrime 10^3;
   P4=kk[x_0..x_4];
   X=abelianSurfaceD15 P4;
   (d,sg)=(degree X, sectionalGenus X)
   minimalBetti X
   betti (T=tateResolutionOfSurface(X,7))
   HdotK(d,sg)==25
   xO=chiO(X)
   Ksquare(d,sg,xO)==-25
  Text
   X is a non-minimal abelian surface. it contains twentyfive (-1) lines.
   X is linked via two quintics to a Horrocks-Mumford surface Y.
  Example
   ci=ideal(gens X* random(source gens X,P4^{2:-5}));
   Y=ci:X;
   minimalBetti Y
   (degree Y, sectionalGenus Y) == (10,6)
   betti tateResolutionOfSurface(Y,7)
*-

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
   The construction uses this liason.
  CannedExample
   i1 : kk=ZZ/nextPrime 10^3;
   i2 : P4=kk[x_0..x_4];
   i3 : X=abelianSurfaceD15 P4;

   o3 : Ideal of P4
   i4 : (d,sg)=(degree X, sectionalGenus X)

   o4 = (15, 21)

   o4 : Sequence
   i5 : minimalBetti X

               0 1  2  3 4
   o5 = total: 1 8 15 10 2
            0: 1 .  .  . .
	    1: . .  .  . .
	    2: . .  .  . .
	    3: . .  .  . .
	    4: . 3  .  . .
	    5: . .  .  . .
	    6: . 5 15 10 2

   o5 : BettiTally
   i6 : betti (T=tateResolutionOfSurface(X,7))

                -1   0  1  2  3  4 5  6  7   8
   o6 = total: 171 105 55 22 11 10 8 17 50 115
           -4:   1   .  .  .  .  . .  .  .   .
	   -3: 170 105 55 20  1  . .  .  .   .
	   -2:   .   .  .  2 10 10 5  .  .   .
	   -1:   .   .  .  .  .  . .  2  .   .
	    0:   .   .  .  .  .  . 3 15 50 115

   o6 : BettiTally
   i7 : HdotK(d,sg)==25

   o7 = true
   i8 : xO=chiO(X)

   o8 = 0
   i9 : Ksquare(d,sg,xO)==-25

   o9 = true
  Text
   X is a non-minimal abelian surface. it contains twentyfive (-1)-lines.
   X is linked via two quintics to a Horrocks-Mumford surface Y.
  CannedExample
   i10 : ci=ideal(gens X* random(source gens X,P4^{2:-5}));

   o10 : Ideal of P4
   i11 : Y=ci:X;

   o11 : Ideal of P4
   i12 : minimalBetti Y

                0  1  2  3 4
   o12 = total: 1 18 35 20 2
             0: 1  .  .  . .
	     1: .  .  .  . .
	     2: .  .  .  . .
	     3: .  .  .  . .
	     4: .  3  .  . .
	     5: . 15 35 20 .
	     6: .  .  .  . 2

   o12 : BettiTally
   i13 : (degree Y, sectionalGenus Y) == (10,6)

   o13 = true
   i14 : betti tateResolutionOfSurface(Y,7)

                -1  0  1 2 3  4  5  6  7   8
   o14 = total: 81 45 20 7 6 10 13 32 85 175
            -4:  1  .  . . .  .  .  .  .   .
	    -3: 80 45 20 5 1  .  .  .  .   .
	    -2:  .  .  . 2 .  .  .  .  .   .
	    -1:  .  .  . . 5 10 10  2  .   .
	     0:  .  .  . . .  .  3 30 85 175

   o14 : BettiTally

References
   \textit{Barth, W., Hulek, K., Moore, R.}, Degenerations of {Horrocks}-{Mumford} surfaces, Math. Ann.,277, (1987), 735--755

   \textit{Horrocks, G., Mumford, D.}, A rank 2 vector bundle on {P}{{\(^4\)}} with 15,000 symmetries, Topology ,212, (1973), 63-81

   \textit{Popescu, S.}, Surfaces of degree $\ge 11$ in the Projective Fourspace, Dissertation, Universit\"at des Saarlandes, (1993) 
SeeAlso
  horrocksMumfordSurface
  adjunctionProcessData
///
-*
  Text
   The surface X is non-mimimal. Adjunction gives
  Example
   betti (HplusK=presentation truncate(1,Ext^1(X,P4^{-5})))
   P19=kk[y_0..y_19];
   P4xP19=P4**P19;
   graph=sub(vars P19,P4xP19)*sub(HplusK,P4xP19);
   betti(presH=map(P19^5,,sub(contract(transpose sub(vars P4,P4xP19),graph),P19)))
   elapsedTime betti(X1=ann coker presH) -- 49.985s elapsed
   minimalBetti X1
  Text
   X1 is the first adjoint surface

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

-* for CannedExample abelianSurfaceD15S21Popescu
  Example
   kk=ZZ/nextPrime 10^4;
   P4=kk[x_0..x_4];
   X=abelianSurfaceD15S21Popescu P4;
   dim singularLocus X == 0 --=> X is smooth
   (d,sg)=(degree X, sectionalGenus X)
   minimalBetti X
   betti tateResolutionOfSurface(X,7)
   HdotK(d,sg)==25
   xO=chiO(X)
   Ksquare(d,sg,xO)==-25
   LeBarzN6(d,sg,xO)

*-
doc ///
Key
 abelianSurfaceD15S21Popescu
 (abelianSurfaceD15S21Popescu, PolynomialRing)
Headline
 construct an abelian surface of degree 15 and sectional genus 21
Usage
 X=abelianSurfaceD15S21Popescu P4
Inputs
 P4:PolynomialRing
  coordinate ring of P4
Outputs
 X:Ideal
  of an abelian surface of degree 15 and sectional genus 21
Description
  Text
   These surfaces are not linked to Horrocks-Mumford surfaces. The construction builds upon a subtle
   use of three Moore matrices.
  CannedExample
    i1 : kk=ZZ/nextPrime 10^4;
    i2 : P4=kk[x_0..x_4];
    i3 : X=abelianSurfaceD15S21Popescu P4;

    o3 : Ideal of P4
    i4 : dim singularLocus X == 0 --=> X is smooth

    o4 = true
    i5 : (d,sg)=(degree X, sectionalGenus X)

    o5 = (15, 21)

    o5 : Sequence
    i6 : minimalBetti X

                0  1  2 3
    o6 = total: 1 11 15 5
             0: 1  .  . .
	     1: .  .  . .
	     2: .  .  . .
	     3: .  .  . .
	     4: .  1  . .
	     5: . 10 15 5

    o6 : BettiTally
    i7 : betti tateResolutionOfSurface(X,7)

                 -1   0  1  2  3  4 5  6  7   8
    o7 = total: 171 105 55 22 11 10 6 15 50 115
            -4:   1   .  .  .  .  . .  .  .   .
	    -3: 170 105 55 20  1  . .  .  .   .
	    -2:   .   .  .  2 10 10 5  .  .   .
	    -1:   .   .  .  .  .  . .  .  .   .
	     0:   .   .  .  .  .  . 1 15 50 115

    o7 : BettiTally
    i8 : HdotK(d,sg)==25

    o8 = true
    i9 : xO=chiO(X)

    o9 = 0
    i10 : Ksquare(d,sg,xO)==-25

    o10 = true
    i11 : LeBarzN6(d,sg,xO)

    o11 = 25
  Text
   X is a non-minimal abelian surface. It contains twenty five (-1) lines.
References
   \textit{Popescu, S.}, Surfaces of degree $\ge 11$ in the Projective Fourspace, Dissertation, Universit\"at des Saarlandes, (1993)    
SeeAlso
  horrocksMumfordSurface
  abelianSurfaceD15
///
-*
   ci=ideal(gens X*random(source gens X,P4^{-5,-6}));
   Y=ci:X;
   minimalBetti Y
   d=degree Y, sg=sectionalGenus Y
   xO=chiO(Y)
   Ksquare(d,sg,xO)
   betti tateResolutionOfSurface(Y,8)
*-

-* for CannedExample ellipticSurfaceD7
 Example
   kk=ZZ/nextPrime 10^3;
   P4=kk[x_0..x_4];
   elapsedTime X=ellipticSurfaceD7 P4;
   (d,sg)=(degree X, sectionalGenus X)
   minimalBetti X
   betti(T=tateResolutionOfSurface X)
*-

doc ///
Key
 ellipticSurfaceD7
 (ellipticSurfaceD7,PolynomialRing)
Headline
 construct an elliptic surface of degree 7 
Usage
 X=ellipticSurfaceD7 P4
Inputs
 P4:PolynomialRing
  coordinate ring of P4
Outputs
 X:Ideal
  of an elliptic surface of degree 7 
Description
  Text
  CannedExample
    i1 : kk=ZZ/nextPrime 10^3;
    i2 : P4=kk[x_0..x_4];
    i3 : elapsedTime X=ellipticSurfaceD7 P4;
    -- .00401666s elapsed

    o3 : Ideal of P4
    i4 : (d,sg)=(degree X, sectionalGenus X)

    o4 = (7, 6)

    o4 : Sequence
    i5 : minimalBetti X

                0 1 2
    o5 = total: 1 3 2
             0: 1 . .
	     1: . 1 .
	     2: . . .
	     3: . 2 2

    o5 : BettiTally
    i6 : betti(T=tateResolutionOfSurface X)

                -1  0  1 2 3  4  5  6   7
    o6 = total: 66 39 20 9 7 17 43 90 166
            -4:  1  .  . . .  .  .  .   .
	    -3: 65 39 20 8 2  .  .  .   .
	    -2:  .  .  . . .  .  .  .   .
	    -1:  .  .  . . .  .  .  .   .
	     0:  .  .  . 1 5 17 43 90 166

    o6 : BettiTally
 Text
   The surface is ACM. We use its Hilbert-Burch matrix.
References
   \textit{Ionescu, P.} Embedded projective varieties of small invariants III, Proceedings of the l'Aquila conference. LNM., 1417, (1990), 138-154
SeeAlso
  tateResolutionOfSurface
///

-* for CannedExample ellipticSurfaceD8
Example
   kk=ZZ/nextPrime 10^3;
   P4=kk[x_0..x_4];
   elapsedTime X=ellipticSurfaceD8 P4;
   (d,sg)=(degree X, sectionalGenus X)
   minimalBetti X
   betti(T=tateResolutionOfSurface X)
   pg=rank HH^2(sheaf(P4/X))

*-
doc ///
Key
 ellipticSurfaceD8
 (ellipticSurfaceD8,PolynomialRing)
Headline
 construct an elliptic surface of degree 8 
Usage
 X=ellipticSurfaceD8 P4
Inputs
 P4:PolynomialRing
  coordinate ring of P4
Outputs
 X:Ideal
  of an elliptic surface of degree 8 
Description
  Text
  CannedExample
    i1 : kk=ZZ/nextPrime 10^3;
    i2 : P4=kk[x_0..x_4];
    i3 : elapsedTime X=ellipticSurfaceD8 P4;
    -- .00584715s elapsed

    o3 : Ideal of P4
    i4 : (d,sg)=(degree X, sectionalGenus X)

    o4 = (8, 7)

    o4 : Sequence
    i5 : minimalBetti X

                0 1 2
    o5 = total: 1 3 2
             0: 1 . .
	     1: . . .
	     2: . 2 .
	     3: . 1 2

    o5 : BettiTally
    i6 : betti(T=tateResolutionOfSurface X)

                -1  0  1 2 3  4  5  6   7
    o6 = total: 76 45 23 9 4 11 33 75 145
            -4:  1  .  . . .  .  .  .   .
	    -3: 75 45 23 9 2  .  .  .   .
	    -2:  .  .  . . .  .  .  .   .
	    -1:  .  .  . . .  .  .  .   .
	     0:  .  .  . . 2 11 33 75 145

    o6 : BettiTally
    i7 : pg=rank HH^2(sheaf(P4/X))

    o7 = 2
 Text
   The surface is ACM. We use its Hilbert-Burch matrix.
References
   \textit{Ionescu, P.} Embedded projective varieties of small invariants III, Proceedings of the l'Aquila conference. LNM., 1417, (1990), 138-154
   \textit{Okonek, Ch.} Fl\"achen vom Grad 8 in $\Pn 4$, Math. Z., 191, (1986), 207-223
SeeAlso
  tateResolutionOfSurface
///

-* for CannedExample ellipticSurfaceD9
  Example
    new BettiTally from {(0,{2},2) => 2, (1,{3},3) => 7, (2,{4},4) => 5, (2,{5},5) =>10}
  Text
    We take the dependency locus of a homomorphism from F=3O(-4)++O(-5) to G.
  Example
   kk=ZZ/nextPrime 10^3;
   P4=kk[x_0..x_4];
   elapsedTime X=ellipticSurfaceD9 P4;
   (degree X, sectionalGenus X)==(9,7)
   minimalBetti X
   betti(T=tateResolutionOfSurface X)
   pg=rank HH^2(sheaf(P4/X))
   Ksquare(9,7,2)==0
   D=saturate canonicalDivisor X;
   betti D, degree D
   HdotK(9,7)==degree D
   selfIntersectionNumber(X,D)
*-

doc ///
Key
 ellipticSurfaceD9
 (ellipticSurfaceD9,PolynomialRing)
Headline
 construct an elliptic surface of degree 9 
Usage
 X=ellipticSurfaceD9 P4
Inputs
 P4:PolynomialRing
  coordinate ring of P4
Outputs
 X:Ideal
  of an elliptic surface of degree 9 
Description
  Text
    The syzygy bundle G of the desired H^1-module has rank 5
    and a presentation 7x15 matrix 
  CannedExample
    i1 : new BettiTally from {(0,{2},2) => 2, (1,{3},3) => 7, (2,{4},4) => 5, (2,{5},5) =>10}

                0 1  2
    o1 = total: 2 7 15
             2: 2 7  5
             3: . . 10

    o1 : BettiTally
  Text
    We take the dependency locus of a homomorphism from F=3O(-4)++O(-5) to G.
  CannedExample
    i2 : kk=ZZ/nextPrime 10^3;
    i3 : P4=kk[x_0..x_4];
    i4 : elapsedTime X=ellipticSurfaceD9 P4;
    -- .0511618s elapsed

    o4 : Ideal of P4
    i5 : (degree X, sectionalGenus X)==(9,7)

    o5 = true
    i6 : minimalBetti X

                0  1  2  3 4
    o6 = total: 1 11 20 13 3
             0: 1  .  .  . .
	     1: .  .  .  . .
	     2: .  .  .  . .
	     3: .  2  .  . .
	     4: .  9 20 13 3

    o6 : BettiTally
    i7 : betti(T=tateResolutionOfSurface X)

                -1  0  1 2 3 4  5  6   7
    o7 = total: 81 47 23 8 3 5 19 55 118
            -4:  1  .  . . . .  .  .   .
            -3: 80 47 23 8 1 .  .  .   .
	    -2:  .  .  . . . .  .  .   .
	    -1:  .  .  . . 2 3  .  .   .
	     0:  .  .  . . . 2 19 55 118

    o7 : BettiTally
    i8 : pg=rank HH^2(sheaf(P4/X))

    o8 = 1
    i9 : Ksquare(9,7,2)==0

    o9 = true
    i10 : D=saturate canonicalDivisor X;

    o10 : Ideal of P4
    i11 : betti D, degree D

                  0 1
    o11 = (total: 1 3, 3)
               0: 1 2
               1: . .
	       2: . 1

    o11 : Sequence
    i12 : HdotK(9,7)==degree D

    o12 = true
    i13 : selfIntersectionNumber(X,D)

    o13 = 0
  Text
   X is a minimal elliptic surface.
References
   \textit{Aure, A., Ranestad, K} The Smooth Surfaces of Degree $9$ in $\Pn 4$, LNS,London Math. Soc.,Cambridge Univ. Press, 179, (1992) 32-46
SeeAlso
  tateResolutionOfSurface
  canonicalDivisor
  selfIntersectionNumber
  Ksquare
///

-* For CannedEcample of ellipticSurfaceD10S9
 Example
   kk=ZZ/nextPrime 10^3;
   P4=kk[x_0..x_4];
   setRandomSeed(" fix the decomposition of the canonicalDivisor");
   elapsedTime X=ellipticSurfaceD10S9 P4;
   (degree X, sectionalGenus X)==(10,9)
   minimalBetti X
   betti(T=tateResolutionOfSurface X)
   pg=rank HH^2(sheaf(P4/X))
   LeBarzN6(10,9,2)
   HdotK(10,9)
   Ksquare(10,9,2)
   D=saturate canonicalDivisor X;
   apply(primaryDecomposition D,c->(dim c,degree c,genus c,selfIntersectionNumber(X,c)))
*-

doc ///
Key
 ellipticSurfaceD10S9
 (ellipticSurfaceD10S9,PolynomialRing)
Headline
 construct an elliptic surface of degree 10 and sectional genus 9
Usage
 X=ellipticSurfaceD10S9 P4
Inputs
 P4:PolynomialRing
  coordinate ring of P4
Outputs
 X:Ideal
  of an elliptic surface of degree 10 and sectional genus 9 
Description
  Text
   We construct an elliptic surface of degree 10 and sectional genus 9
  CannedExample
    i2 :    kk=ZZ/nextPrime 10^3;
    i3 :    P4=kk[x_0..x_4];
    i4 :    setRandomSeed(" fix the decomposition of the canonicalDivisor");
       -- setting random seed to 51670537354572222457359509835439844926907858937134012131891195733955819925382916224591497751
    i5 :    elapsedTime X=ellipticSurfaceD10S9 P4;
       -- .421647s elapsed

    o5 : Ideal of P4
    i6 :    (degree X, sectionalGenus X)==(10,9)

    o6 = true
    i7 :    minimalBetti X

                0  1  2 3 4
    o7 = total: 1 10 15 7 1
             0: 1  .  . . .
             1: .  .  . . .
             2: .  .  . . .
             3: .  1  . . .
             4: .  9 14 5 .
             5: .  .  1 2 1

    o7 : BettiTally
    i8 :    betti(T=tateResolutionOfSurface X)

                -1  0  1  2 3 4  5  6   7
    o8 = total: 95 56 28 10 3 4 15 46 104
            -4:  1  .  .  . . .  .  .   .
            -3: 94 56 28 10 1 .  .  .   .
            -2:  .  .  .  . 1 .  .  .   .
            -1:  .  .  .  . 1 3  1  .   .
             0:  .  .  .  . . 1 14 46 104
    o8 : BettiTally
    i9 :    pg=rank HH^2(sheaf(P4/X))

    o9 = 1
    i10 :    LeBarzN6(10,9,2)

    o10 = 3
    i11 :    HdotK(10,9)

    o11 = 6
    i12 :    Ksquare(10,9,2)

    o12 = -3
    i13 :    D=saturate canonicalDivisor X;

    o13 : Ideal of P4
    i14 :    apply(primaryDecomposition D,c->(dim c,degree c,genus c,selfIntersectionNumber(X,c)))

    o14 = {(2, 3, 1, 0), (2, 3, -2, -3)}
    o14 : List
 Text
   X is non-minimal elliptic surface blown-up in three points.
References
   \textit{Ranestad, K} On smooth surfaces of degree ten in the projective fourspace, Thesis, Univ of Oslo, (1988)
SeeAlso
  tateResolutionOfSurface
  canonicalDivisor
  selfIntersectionNumber
  Ksquare
  LeBarzN6
///

-*
For CannedExample of ellipticSurfaceD10S10
  Example
   kk=ZZ/nextPrime 10^3;
   P4=kk[x_0..x_4];
   elapsedTime X=ellipticSurfaceD10S10 P4;
   (degree X, sectionalGenus X)==(10,10)
   minimalBetti X
   betti(T=tateResolutionOfSurface X)
   pg=rank HH^2(sheaf(P4/X))
   LeBarzN6(10,10,3)   
   D=saturate canonicalDivisor X;
   tally apply(primaryDecomposition D,c->
       (dim c,degree c,genus c,minimalBetti c,selfIntersectionNumber(X,c)))
   HdotK(10,10)==2+6
   Ksquare(10,10,3)==-2

*-

doc ///
Key
 ellipticSurfaceD10S10
 (ellipticSurfaceD10S10,PolynomialRing)
Headline
 construct an elliptic surface of degree 10 and sectional genus 10
Usage
 X=ellipticSurfaceD10S10 P4
Inputs
 P4:PolynomialRing
  coordinate ring of P4
Outputs
 X:Ideal
  of an elliptic surface of degree 10 and sectional genus 10 
Description
  Text
    We construct an elliptic surface of degree 10 and sectional genus 10 and pg=2.
  CannedExample
    i2 :    kk=ZZ/nextPrime 10^3;
    i3 :    P4=kk[x_0..x_4];
    i4 :    elapsedTime X=ellipticSurfaceD10S10 P4;
      -- .0825116s elapsed

    o4 : Ideal of P4
    i5 :    (degree X, sectionalGenus X)==(10,10)

    o5 = true
    i6 :    minimalBetti X

                0 1 2 3 4
    o6 = total: 1 6 9 5 1
             0: 1 . . . .
             1: . . . . .
             2: . . . . .
             3: . 3 . . .
             4: . 3 9 5 1
    o6 : BettiTally
    i7 :    betti(T=tateResolutionOfSurface X)

                 -1  0  1  2 3 4  5  6   7
    o7 = total: 100 60 31 12 3 4 18 51 110
            -4:   1  .  .  . . .  .  .   .
            -3:  99 60 31 12 2 .  .  .   .
            -2:   .  .  .  . 1 .  .  .   .
            -1:   .  .  .  . . 1  .  .   .
             0:   .  .  .  . . 3 18 51 110

    o7 : BettiTally
    i8 :    pg=rank HH^2(sheaf(P4/X))

    o8 = 2
    i9 :    LeBarzN6(10,10,3)

    o9 = 2
    i10 :    D=saturate canonicalDivisor X;

    o10 : Ideal of P4
    i11 :    tally apply(primaryDecomposition D,c->
             (dim c,degree c,genus c,minimalBetti c,selfIntersectionNumber(X,c)))

                                  0 1 2 3 4
    o11 = Tally{(2, 2, -1, total: 1 5 8 5 1, -2) => 1}
                               0: 1 1 . . .
                               1: . 4 8 5 1
                                 0 1 2 3 4
                (2, 6, 1, total: 1 5 9 6 1, 0) => 1
                              0: 1 . . . .
                              1: . 3 . . .
                              2: . 2 9 6 1
    o11 : Tally
    i12 :    HdotK(10,10)==2+6

    o12 = true
    i13 :    Ksquare(10,10,3)==-2

    o13 = true
 Text
   X is elliptic surface blown-up with two (-1) lines.
References
   \textit{Ranestad, K} On smooth surfaces of degree ten in the projective fourspace, Thesis, Univ of Oslo, (1988)

SeeAlso
  tateResolutionOfSurface
  canonicalDivisor
  HdotK
  Ksquare
  LeBarzN6
///


-* For CannedExample of ellipticSurfaceD11S12
Example
   kk=ZZ/nextPrime 10^3;
   P4=kk[x_0..x_4];
   elapsedTime X=ellipticSurfaceD11S12 P4;
   (degree X, sectionalGenus X)==(11,12)
   minimalBetti X
   betti(T=tateResolutionOfSurface X)
   pg=rank HH^2(sheaf(P4/X))
   D=saturate canonicalDivisor X;
   tally apply(primaryDecomposition D,c->
       (dim c,degree c,genus c,minimalBetti c,selfIntersectionNumber(X,c)))
   LeBarzN6(11,12,3)==3
   HdotK(11,12)==3+6+2
   Ksquare(11,12,3)

*-

doc ///
Key
 ellipticSurfaceD11S12
 (ellipticSurfaceD11S12,PolynomialRing)
Headline
 construct an elliptic surface of degree 11 and sectional genus 12
Usage
 X=ellipticSurfaceD11S12 P4
Inputs
 P4:PolynomialRing
  coordinate ring of P4
Outputs
 X:Ideal
  of an elliptic surface of degree 11 and sectional genus 12.
Description
  Text
    We construct an elliptic surface of degree 11 and sectional genus 12 and pg=2.
  CannedExample
    i2 :    kk=ZZ/nextPrime 10^3;
    i3 :    P4=kk[x_0..x_4];
    i4 :    elapsedTime X=ellipticSurfaceD11S12 P4;
       -- .093704s elapsed

    o4 : Ideal of P4
    i5 :    (degree X, sectionalGenus X)==(11,12)

    o5 = true
    i6 :    minimalBetti X

                0 1  2 3 4
    o6 = total: 1 9 13 6 1
             0: 1 .  . . .
             1: . .  . . .
             2: . .  . . .
             3: . 1  . . .
             4: . 8 13 6 1
    o6 : BettiTally
    i7 :    betti(T=tateResolutionOfSurface X)

                 -1  0  1  2 3 4  5  6  7
    o7 = total: 114 69 36 14 4 3 13 42 96
            -4:   1  .  .  . . .  .  .  .
            -3: 113 69 36 14 2 .  .  .  .
            -2:   .  .  .  . 2 1  .  .  .
            -1:   .  .  .  . . 1  .  .  .
             0:   .  .  .  . . 1 13 42 96
    o7 : BettiTally
    i8 :    pg=rank HH^2(sheaf(P4/X))

    o8 = 2
    i9 :    D=saturate canonicalDivisor X;

    o9 : Ideal of P4
    i10 :    tally apply(primaryDecomposition D,c->
             (dim c,degree c,genus c,minimalBetti c,selfIntersectionNumber(X,c)))

                                 0 1  2 3 4
    o10 = Tally{(2, 6, 1, total: 1 6 11 8 2, 0) => 1}
                              0: 1 1  . . .
                              1: . .  . . .
                              2: . 2  2 . .
                              3: . 3  9 8 2
                                 0 1 2 3
                (2, 1, 0, total: 1 3 3 1, -1) => 3
                              0: 1 3 3 1
                                 0 1 2 3
                (2, 2, 0, total: 1 3 3 1, -1) => 1
                              0: 1 2 1 .
                              1: . 1 2 1
    o10 : Tally
    i11 :    LeBarzN6(11,12,3)==3

    o11 = true
    i12 :    HdotK(11,12)==3+6+2

    o12 = true
    i13 :    Ksquare(11,12,3)

     o13 = -4
   Text
   X is an elliptic surface blown-up with three (-1) lines and one (-1) conic.
References
   \textit{Popescu, S.}, Surfaces of degree $\ge 11$ in the Projective Fourspace, Dissertation, Universit\"at des Saarlandes, (1993)
SeeAlso
  tateResolutionOfSurface
  canonicalDivisor
  HdotK
  Ksquare          
  LeBarzN6
///


-* for CannedExample in ellipticSurfaceD12S14L0
  Example
   kk=ZZ/nextPrime 10^3;
   P4=kk[x_0..x_4];
   setRandomSeed("fix decomposition of the canonical divisors");
   elapsedTime X=ellipticSurfaceD12S14L0 P4;
   (degree X, sectionalGenus X)==(12,14)
   minimalBetti X
   betti(T=tateResolutionOfSurface X)
   pg=1+(genera X)_0
   D1=saturate canonicalDivisor X;
   degree D1,HdotK(12,14)
   selfIntersectionNumber(X,D1),Ksquare(12,14,3)
   D2=saturate canonicalDivisor X;
   E=saturate(D1+D2);
   degree E
   cE=decompose E;
   tally apply(cE,c->(degree c, genus c, selfIntersectionNumber(X,c)))
   Dmin=D1:E;
   HH^0 (sheaf (P4^1/Dmin))
*-

doc ///
Key
 ellipticSurfaceD12S14L0
 (ellipticSurfaceD12S14L0,PolynomialRing)
Headline
 construct an elliptic surface of degree 12, sectional genus 14 and no 6-secant line
Usage
 X=ellipticSurfaceD12S12L0 P4
Inputs
 P4:PolynomialRing
  coordinate ring of P4
Outputs
 X:Ideal
  of an elliptic surface of degree 12 and sectional genus 14 
Description
  Text
    We construct an elliptic surface of degree 12, sectional genus 14 and no 6-secant line.
  CannedExample
   i1 : kk=ZZ/nextPrime 10^3;
   i2 : P4=kk[x_0..x_4];
   i3 : setRandomSeed("fix decomposition of the canonical divisors");
     -- setting random seed to 156513424253060481162377452610506080227701333709335531157084021625895990393353946085745
   i4 : elapsedTime X=ellipticSurfaceD12S14L0 P4;
     -- .853767s elapsed

   o4 : Ideal of P4
   i5 : (degree X, sectionalGenus X)==(12,14)

   o5 = true
   i6 : minimalBetti X

               0 1  2 3 4
   o6 = total: 1 8 11 5 1
            0: 1 .  . . .
	    1: . .  . . .
	    2: . .  . . .
	    3: . .  . . .
	    4: . 8  7 1 .
	    5: . .  4 4 1

   o6 : BettiTally
   i7 : betti(T=tateResolutionOfSurface X)

                -1  0  1  2 3 4 5  6  7
   o7 = total: 128 78 41 16 5 3 9 33 82
           -4:   1  .  .  . . . .  .  .
	   -3: 127 78 41 16 2 . .  .  .
	   -2:   .  .  .  . 3 2 .  .  .
	   -1:   .  .  .  . . 1 1  .  .
	    0:   .  .  .  . . . 8 33 82

   o7 : BettiTally
   i8 : pg=1+(genera X)_0

   o8 = 3
   i9 : D1=saturate canonicalDivisor X;

   o9 : Ideal of P4
   i10 : degree D1,HdotK(12,14)

   o10 = (14, 14)

   o10 : Sequence
   i11 : selfIntersectionNumber(X,D1),Ksquare(12,14,3)

   o11 = (-5, -5)

   o11 : Sequence
   i12 : D2=saturate canonicalDivisor X;

   o12 : Ideal of P4
   i13 : E=saturate(D1+D2);

   o13 : Ideal of P4
   i14 : degree E

   o14 = 6
   i15 : cE=decompose E;
   i16 : tally apply(cE,c->(degree c, genus c, selfIntersectionNumber(X,c)))

   o16 = Tally{(1, 0, -1) => 4}
               (2, 0, -1) => 1

   o16 : Tally
   i17 : Dmin=D1:E;

   o17 : Ideal of P4
   i18 : HH^0 (sheaf (P4^1/Dmin))

           1
   o18 = kk

   o18 : kk-module, free
  Text
   X is an non-minimal elliptic surface with four (-1)-lines and one  (-1)-conic curve.
   X has a fibration into a pencil of elliptic curves of degree 8.
References
   \textit{Popescu, S.}, Surfaces of degree $\ge 11$ in the Projective Fourspace, Dissertation, Universit\"at des Saarlandes, (1993)
SeeAlso
  tateResolutionOfSurface
  canonicalDivisor
  selfIntersectionNumber
  Ksquare
  LeBarzN6
///

-* for CannedExample of ellipticSurfaceD12S14Linfinite
Example
   kk=ZZ/nextPrime 10^3;
   P4=kk[x_0..x_4];
   elapsedTime X=ellipticSurfaceD12S14Linfinite P4;
   (degree X, sectionalGenus X)==(12,14)
   minimalBetti X
   betti(T=tateResolutionOfSurface X)
   LeBarzN6(12,14,3)
   HdotK(12,14)
   Ksquare(12,14,3)
   R=residualInQuintics X;
   dim R, degree R ,betti R, degree (R+X)
   apply(primaryDecomposition(R+X),c->(dim c ,degree c, betti c))
*-

doc ///
Key
 ellipticSurfaceD12S14Linfinite
 (ellipticSurfaceD12S14Linfinite,PolynomialRing)
Headline
 construct an elliptic surface of degree 12, sectional genus 14 and infinitly many 6-secant line
Usage
 X=ellipticSurfaceD12S14Linfinite P4
Inputs
 P4:PolynomialRing
  coordinate ring of P4
Outputs
 X:Ideal
  of an elliptic surface of degree 12 and sectional genus 14 
Description
  Text
   We construct a regular elliptic surface of degree 12, sectional genus 14 and pg=2.
  CannedExample
    i2 :    kk=ZZ/nextPrime 10^3;
    i3 :    P4=kk[x_0..x_4];
    i4 :    elapsedTime X=ellipticSurfaceD12S14Linfinite P4;
        -- 2.22857s elapsed

    o4 : Ideal of P4
    i5 :    (degree X, sectionalGenus X)==(12,14)

    o5 = true
    i6 :    minimalBetti X

                0  1  2 3 4
    o6 = total: 1 10 14 6 1
             0: 1  .  . . .
             1: .  .  . . .
             2: .  .  . . .
             3: .  .  . . .
             4: .  8  9 2 .
             5: .  2  5 4 1
    o6 : BettiTally
    i7 :    betti(T=tateResolutionOfSurface X)

                 -1  0  1  2 3 4 5  6  7
    o7 = total: 128 78 41 16 5 3 9 33 82
            -4:   1  .  .  . . . .  .  .
            -3: 127 78 41 16 2 . .  .  .
            -2:   .  .  .  . 3 2 .  .  .
            -1:   .  .  .  . . 1 1  .  .
             0:   .  .  .  . . . 8 33 82
    o7 : BettiTally
    i8 :    LeBarzN6(12,14,3)

    o8 = 4
    i9 :    HdotK(12,14)

    o9 = 14
    i10 :    Ksquare(12,14,3)

    o10 = -5
    i11 :    R=residualInQuintics X;

    o11 : Ideal of P4
    i12 :    dim R, degree R ,betti R, degree (R+X)

                        0 1
    o12 = (3, 1, total: 1 2, 5)
                     0: 1 2
    o12 : Sequence
    i13 :    apply(primaryDecomposition(R+X),c->(dim c ,degree c, betti c))

                         0 1                 0 1
    o13 = {(2, 5, total: 1 3), (1, 1, total: 1 4)}
                      0: 1 2              0: 1 4
                      1: . .
                      2: . .
                      3: . .
                      4: . 1
    o13 : List
 Text
   X contains a plane quintic curve with an additional point p in that plane.
   Every line through p in that plane is a 6-secant line.
References
   \textit{Popescu, S.}, Surfaces of degree $\ge 11$ in the Projective Fourspace, Dissertation, Universit\"at des Saarlandes, (1993)
SeeAlso
  tateResolutionOfSurface
  residualInQuintics
  Ksquare
  LeBarzN6
///
-* for CannedExample of ellipticSurfaceD12S13
 Example
   kk=ZZ/nextPrime 10^4; 
   P4=kk[x_0..x_4];
   X=ellipticSurfaceD12S13 P4;
   (d,sg)=(degree X, sectionalGenus X)
   minimalBetti X
   betti(T=tateResolutionOfSurface X)
   Ksquare(d,sg,3)
   D=saturate canonicalDivisor X; 
   HdotK(d,sg)
   degree D
   rank HH^0 sheaf(P4^1/D)
   selfIntersectionNumber(X,D)
   genus D
   singD=singularLocus(P4/D); dim singD==0 -- 9.57484s elapsed
   minimalBetti D

*-

doc ///
Key
 ellipticSurfaceD12S13
 (ellipticSurfaceD12S13,PolynomialRing)
Headline
 construct a regular elliptic surface of degree 12 and sectional genus 13
Usage
 X=ellipticSurfaceD12S13 P4
Inputs
 P4:PolynomialRing
  coordinate ring of P4
Outputs
 X:Ideal
  of a regular elliptic surface of degree 12 and sectional genus 13
Description
  Text
   We construct a regular elliptic surface of degree 12, sectional genus 13 and pg=2.
 
  CannedExample 
    i2 :    kk=ZZ/nextPrime 10^4; 
    i3 :    P4=kk[x_0..x_4];
    i4 :    X=ellipticSurfaceD12S13 P4;

    o4 : Ideal of P4
    i5 :    (d,sg)=(degree X, sectionalGenus X)

    o5 = (12, 13)
    o5 : Sequence
    i6 :    minimalBetti X

                0  1  2  3 4
    o6 = total: 1 15 30 21 5
             0: 1  .  .  . .
             1: .  .  .  . .
             2: .  .  .  . .
             3: .  .  .  . .
             4: .  3  .  . .
             5: . 12 30 21 5
    o6 : BettiTally
    i7 :    betti(T=tateResolutionOfSurface X)

                 -1  0  1  2 3 4 5  6  7
    o7 = total: 124 75 39 15 4 4 8 27 75
            -4:   1  .  .  . . . .  .  .
            -3: 123 75 39 15 2 . .  .  .
            -2:   .  .  .  . 2 . .  .  .
            -1:   .  .  .  . . 4 5  .  .
             0:   .  .  .  . . . 3 27 75
    o7 : BettiTally
    i8 :    Ksquare(d,sg,3)

    o8 = 0
    i9 :    D=saturate canonicalDivisor X; 

    o9 : Ideal of P4
   i10 :    HdotK(d,sg)

   o10 = 12
   i11 :    degree D

   o11 = 12
   i12 :    rank HH^0 sheaf(P4^1/D)

   o12 = 1
   i13 :    selfIntersectionNumber(X,D)

   o13 = 0
   i14 :    genus D

   o14 = 1
   i15 :    singD=singularLocus(P4/D); dim singD==0 -- 9.57484s elapsed

   o16 = true
   i17 :    minimalBetti D

                0 1  2  3 4
   o17 = total: 1 8 21 20 6
             0: 1 .  .  . .
             1: . 1  .  . .
             2: . .  .  . .
             3: . 7  4  . .
             4: . . 17 20 6
   o17 : BettiTally
 Text
   Since K^2=0 and the canonical divisor connected this surface is minimal. The surface is elliptic fibration over P1 into
   elliptic curves of degree 12.
References
   \textit{Popescu, S.}, Surfaces of degree $\ge 11$ in the Projective Fourspace, Dissertation, Universit\"at des Saarlandes, (1993)
SeeAlso
  tateResolutionOfSurface
  selfIntersectionNumber
  canonicalDivisor
  HdotK
  Ksquare
///


doc ///
Key
 specificEllipticSurfaceD13S16
 (specificEllipticSurfaceD13S16,PolynomialRing,Ring, ZZ)
 [specificEllipticSurfaceD13S16,Verbose]
Headline
 construct a specific elliptic surface via linkage form an Abo surface (4 families)
Usage
 X=specificEllipticSurfaceD13S16(P4,E,k)
Inputs
 P4:PolynomialRing
  coordinate ring of P4
 E: Ring
   exterior algebra dual to P4
 k: ZZ
   the number of the specific Abo surface used in the construction.
Outputs
 X:Ideal
  of a specific elliptic surface of degree 13 sectional genus 16
Description
  Text
   We construct a specific elliptic surface of degree 13 sectional genus 16 from
   a specficAboSurface of number k via linkage. The function needs the ground field
   kk=ZZ/19 and a number k in {1,2,4,6}.
  CannedExample
   i1 : kk=ZZ/19;
   i2 : P4=kk[x_0..x_4];
   i3 : E=kk[e_0..e_4,SkewCommutative=>true];
   i4 : setRandomSeed("faily fast");
   -- setting random seed to 112617642158795623495
   i5 : X=specificEllipticSurfaceD13S16(P4,E,2,Verbose=>true);
   (K,R) = ({1, 1, 1, 3, 3, 3}, Tally{((2, 1), (1, 6)) => 4 }), dim Hom = 1
                                      ((2, 4), (1, 21)) => 1

   o5 : Ideal of P4

  Text
   The printed information is the partition type of canonical divisor of the specific Abo surface used and
   its redidualInQuintics decomposition, which in this case consists of four 6-secant lines and
   a rational normal curve of degree 4 which is 21-secant.
  CannedExample
   i6 : minimalBetti X

               0  1  2  3 4
   o6 = total: 1 12 22 14 3
            0: 1  .  .  . .
	    1: .  .  .  . .
	    2: .  .  .  . .
	    3: .  .  .  . .
	    4: .  3  .  . .
	    5: .  9 22 14 3

   o6 : BettiTally
   i7 : betti(T=tateResolutionOfSurface(X))

                -1  0  1  2 3 4 5  6  7
   o7 = total: 142 87 46 18 6 4 6 24 68
           -4:   1  .  .  . . . .  .  .
	   -3: 141 87 46 18 2 . .  .  .
	   -2:   .  .  .  . 4 3 .  .  .
	   -1:   .  .  .  . . 1 3  .  .
	    0:   .  .  .  . . . 3 24 68

   o7 : BettiTally
   i8 : (d,sg)=(degree X, sectionalGenus X)

   o8 = (13, 16)

   o8 : Sequence
   i9 : Ksquare(d,sg,3)

   o9 = -5
   i10 : HdotK(d,sg)

   o10 = 17
   i11 : K1=canonicalDivisor X;

   o11 : Ideal of P4
   i12 : K2=canonicalDivisor X;

   o12 : Ideal of P4
   i13 : betti(baseLocus=saturate (K1+K2))

                0 1
   o13 = total: 1 9
             0: 1 .
             1: . .
	     2: . 6
	     3: . 3

   o13 : BettiTally
   i14 : cBaseLocus=decompose baseLocus;
   i15 : minimalBetti last cBaseLocus

                0 1 2 3
   o15 = total: 1 6 8 3
             0: 1 . . .
	     1: . 6 8 3

   o15 : BettiTally
   i16 : tally apply(cBaseLocus,c->(dim c, degree c, genus c, selfIntersectionNumber(X,c)))

   o16 = Tally{(2, 1, 0, -1) => 1 }
               (2, 3, -2, -3) => 1
                (2, 4, 0, -1) => 1

   o16 : Tally
  Text
   Note that the exceptional curves of X coincide with the residualInQuintics curves of
   the used Abo surface.
  CannedExample
   i17 : E1=K1:baseLocus;

   o17 : Ideal of P4
   i18 : dim E1, degree E1, genus E1, selfIntersectionNumber(X,E1)

   o18 = (2, 9, 1, 0)

   o18 : Sequence
   i19 : R=residualInQuintics X;

   o19 : Ideal of P4
   i20 : tally apply(decompose R,c->(dim c, degree c, genus c, degree (c+X)))

   o20 = Tally{(2, 3, -2, 18) => 1}
               (2, 9, -2, 48) => 1

   o20 : Tally
 Text
    X contains four (-1) lines and a (-1) degree 4 rational normal curve. The canonical divisor E
    of the minimal surface has genus 1 and self-intersection number 0. Thus X is an elliptic surface.
   
References
   \textit{Abo, H., Ranestad, K., Schreyer, F-O.} Non-general type surfaces in $\Pn 4$, an update, preprint (2026)
SeeAlso
  tateResolutionOfSurface
  selfIntersectionNumber
  canonicalDivisor
  HdotK
  Ksquare
///

///



///
-*
regularInCodimension(1,P4/D)
*-
-*  For CannedExample of irregularEllipticSurfaceD12
 Example
   kk=ZZ/nextPrime 10^4; 
   P4=kk[x_0..x_4];
   setRandomSeed("fix a fast canonical divisor");
   X=irregularEllipticSurfaceD12 P4;
   (d,sg)=(degree X, sectionalGenus X)
   minimalBetti X
   betti(T=tateResolutionOfSurface(X,7))
   Ksquare(d,sg,3)
   "D=saturate canonicalDivisor X;";
   HdotK(d,sg)
   "degree D==HdotK(d,sg)";
   "betti(fD=res D)";
   "M=(coker transpose fD.dd_4)**P4^{-5}";
   "hilbertFunction(0,M)+1==3 -- the number of connected components of D";
   "selfIntersectionNumber(X,D)==0";   


*-
doc ///
Key
 irregularEllipticSurfaceD12
 (irregularEllipticSurfaceD12,PolynomialRing)
Headline
 construct an irregular elliptic surface of degree 12 and sectional genus 13
Usage
 X=irregularEllipticSurfaceD12 P4
Inputs
 P4:PolynomialRing
  coordinate ring of P4
Outputs
 X:Ideal
  of a irregular elliptic surface of degree 12 sectional genus 13
Description
  Text
   We construct an irregular elliptic surface of degree 12 sectional genus 13 and pg=3.
  CannedExample
    i2 :    kk=ZZ/nextPrime 10^4; 
    i3 :    P4=kk[x_0..x_4];
    i4 :    setRandomSeed("fix a fast canonical divisor");
 -- setting random seed to 134812755737665017156720934136292209881691405812662541386
    i5 :    X=irregularEllipticSurfaceD12 P4;

    o5 : Ideal of P4
    i6 :    (d,sg)=(degree X, sectionalGenus X)

    o6 = (12, 13)
    o6 : Sequence
    i7 :    minimalBetti X

                0 1  2 3 4
    o7 = total: 1 9 15 9 2
             0: 1 .  . . .
             1: . .  . . .
             2: . .  . . .
             3: . .  . . .
             4: . 5  2 . .
             5: . 4 10 4 .
             6: . .  3 5 2
    o7 : BettiTally
    i8 :    betti(T=tateResolutionOfSurface(X,7))

                 -1  0  1  2 3 4  5  6  7   8
    o8 = total: 124 75 39 16 6 5 10 29 75 156
            -4:   1  .  .  . . .  .  .  .   .
            -3: 123 75 39 15 3 .  .  .  .   .
            -2:   .  .  .  1 2 1  .  .  .   .
            -1:   .  .  .  . 1 4  5  2  .   .
             0:   .  .  .  . . .  5 27 75 156
    o8 : BettiTally
    i9 :    Ksquare(d,sg,3)

    o9 = 0
    i10 :    HdotK(d,sg)

    o10 = 12
    Text
    Since K^2=0 this surface is minimal. X is fibered in elliptic curves of degree 4=12/3
    The canonical divisor is the pullback of a divisor of degree 3 on the albanese curve, which is
    an elliptic curve. This fits with pg=3.
References
   \textit{Abo, H., Ranestad, K.},  Irregular elliptic surfaces of degree 12 in projective fourspace, Math. Nach., 278, (2005), 511-524
SeeAlso
  tateResolutionOfSurface
  selfIntersectionNumber
  canonicalDivisor
  HdotK
  Ksquare
///


/// -- the linked surface
betti(ci=ideal (gens X*random(source gens X,P4^{2:-5})))
minimalBetti(Y=ci:X)
betti(tateResolutionOfSurface(Y,7))
singY=saturate ideal singularLocus(P4/Y)
dim singY, degree singY,genus singY, minimalBetti singY
csingY=decompose singY
netList apply(csingY,c->(dim c, degree c, genus c, minimalBetti c))
-*
+-----------------------------+
       |                 0 1 2 3     |
o436 = |(2, 1, 0, total: 1 3 3 1)    |
       |              0: 1 3 3 1     |
       +-----------------------------+
       |                  0 1  2 3 4 |
       |(2, 3, -2, total: 1 6 11 8 2)|
       |               0: 1 1  . . . |
       |               1: . 1  1 . . |
       |               2: . 4 10 8 2 |
       +-----------------------------+
       |                  0 1  2 3 4 |
       |(2, 3, -2, total: 1 6 11 8 2)|
       |               0: 1 1  . . . |
       |               1: . 1  1 . . |
       |               2: . 4 10 8 2 |
       +-----------------------------+
*-
///



/// -- residual to X=irregularEllipticSurfaceD12 P4
kk=ZZ/nextPrime 10^4; 
   P4=kk[x_0..x_4];
   setRandomSeed("fix a fast canonical divisor");
   X=irregularEllipticSurfaceD12 P4;
   (d,sg)=(degree X, sectionalGenus X)
   minimalBetti X
   betti(T=tateResolutionOfSurface(X,7))
   Ksquare(d,sg,3)
   ci=ideal(gens X*random(source gens X,P4^{2:-5}));
   Y=ci:X;   
   dim Y, degree Y, sectionalGenus Y
   minimalBetti Y
   betti tateResolutionOfSurface(Y,8)
   Ksquare(13,16,2)
   cY=decompose Y;
   netList apply(cY,c->(dim c,degree c, sectionalGenus c))
   Y1=cY_1;
   dim singularLocus(P4/Y1)
   betti tateResolutionOfSurface Y1
   degree Y1,sectionalGenus Y1
   Ksquare(10,10,4)
   HdotK(10,10)
   D1=saturate canonicalDivisor Y1;
   D2=saturate canonicalDivisor Y1;
   dim D1, degree D1, genus D1
   tally apply(primaryDecomposition (D1+D2),c->(dim c,degree c))
   selfIntersectionNumber(Y1,D1)
   -- => Y1 is a minimal surface of general type
///
-*
rank HH^0((sheaf(P4^1/D))
cD=primaryDecomposition D;  -- 5.2895s elapsed
   cD=select(cD,c-> dim c ==2);
   #cD
   tally apply(cD,c->(dim c,degree c,degree radical c,minimalBetti c))
   matrix apply(cD,c->apply(cD,d->dim (c+d)))
   netList apply(cD,c->(singC=singularLocus(P4/c);
	   (rank HH^0 sheaf(P4^1/c),genus c,degree c,selfIntersectionNumber(X,c),dim singC)))   

*-

-* for CannedExample K3surfaceD6
 Example
   kk=ZZ/nextPrime 10^3;
   P4=kk[x_0..x_4];
   X=K3surfaceD6 P4;
   (d,sg)=(degree X, sectionalGenus X)
   minimalBetti X
   oX=chiO(X)
   Ksquare(d,sg,oX)
   betti tateResolutionOfSurface X
*-
doc ///
Key
 K3surfaceD6
 (K3surfaceD6, PolynomialRing)
Headline
 construct a K3 surface of degree 6
Usage
 X=K3surface6 P4
Inputs
 P4:PolynomialRing
   coordinate ring of P4
Outputs
 X:Ideal
   of a K3 surface of degree 6
Description
  Text
   We construct an K3 surface of degree 6 as a complete intersection of type (2,3).
   X is minimal and has sectional genus 4.
  CannedExample
    i1 : kk=ZZ/nextPrime 10^3;
    i2 : P4=kk[x_0..x_4];
    i3 : X=K3surfaceD6 P4;

    o3 : Ideal of P4
    i4 : (d,sg)=(degree X, sectionalGenus X)

    o4 = (6, 4)

    o4 : Sequence
    i5 : minimalBetti X

                0 1 2
    o5 = total: 1 2 1
             0: 1 . .
	     1: . 1 .
	     2: . 1 .
	     3: . . 1

    o5 : BettiTally
    i6 : oX=chiO(X)

    o6 = 2
    i7 : Ksquare(d,sg,oX)

    o7 = 0
    i8 : betti tateResolutionOfSurface X

                -1  0  1 2 3  4  5   6   7
    o8 = total: 51 29 14 6 7 20 49 100 181
            -4:  1  .  . . .  .  .   .   .
	    -3: 50 29 14 5 1  .  .   .   .
	    -2:  .  .  . . .  .  .   .   .
	    -1:  .  .  . . .  .  .   .   .
	     0:  .  .  . 1 6 20 49 100 181

    o8 : BettiTally

References

SeeAlso
  
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
  of a K3 surface of degree 7
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
   \textit{Ionescu, P.} Embedded projective varieties of small invariants III, Proceedings of the l'Aquila conference. LNM., 1417, (1990), 138-154
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
   \textit{Ionescu, P.} Embedded projective varieties of small invariants III, Proceedings of the l'Aquila conference. LNM., 1417, (1990), 138-154
   \textit{Okonek, Ch.} Fl\"achen vom Grad 8 in $\Pn 4$, Math. Z., 191, (1986), 207-223
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
   \textit{Aure, A., Ranestad, K} The Smooth Surfaces of Degree $9$ in $\Pn 4$, LNS,London Math. Soc.,Cambridge Univ. Press, 179, (1992) 32-46
SeeAlso
  
///
-* for CannedExample in K3surfaceD10S9L1
 Example
   kk=ZZ/nextPrime 10^3;
   P4=kk[x_0..x_4];
   X=K3surfaceD10S9L1 P4;
   (d,sg)=(degree X, sectionalGenus X)
   minimalBetti X
   OX=sheaf(P4^1/X);
   apply(3,i->HH^i(OX))
   Ksquare(degree X,sectionalGenus X,2)
   LeBarzN6(10,9,2)
   HdotK(10,9)
*-
doc ///
Key
 K3surfaceD10S9L1
 (K3surfaceD10S9L1, PolynomialRing)
Headline
 construct a K3 surface of degree 10 and sectional genus 9 with one 6-secant line
Usage
 X=K3surfaceD10S9L1 P4
Inputs
 P4:PolynomialRing
  coordinate ring of P4
Outputs
 X:Ideal
  of a K3 surface of degree 9
Description
  Text
   We construct a K3 surface of degree 10 and sectional genus 9 with one 6-secant line
  CannedExample
    i2 :    kk=ZZ/nextPrime 10^3;
    i3 :    P4=kk[x_0..x_4];
    i4 :    X=K3surfaceD10S9L1 P4;
   
    o4 : Ideal of P4
    i5 : (d,sg)=(degree X, sectionalGenus X)

    o5 = (10, 9)
    o5 : Sequence
    i6 :    minimalBetti X

                0  1  2  3 4
    o6 = total: 1 11 18 10 2
             0: 1  .  .  . .
             1: .  .  .  . .
             2: .  .  .  . .
             3: .  1  .  . .
             4: .  9 15  7 1
             5: .  1  3  3 1
    o6 : BettiTally
    i7 :    OX=sheaf(P4^1/X);
    i8 :    apply(3,i->HH^i(OX))

            1       1
    o8 = {kk , 0, kk }
    o8 : List
    i9 :    Ksquare(degree X,sectionalGenus X,2)

    o9 = -3
    i10 :    LeBarzN6(10,9,2)

    o10 = 3
    i11 :    HdotK(10,9)

    o11 = 6

  Text
   X is non-minimal with two exceptional lines and an exceptional rational quartic curve.
References
   \textit{Popescu, S.}, Surfaces of degree $\ge 11$ in the Projective Fourspace, Dissertation, Universit\"at des Saarlandes, (1993)  
SeeAlso
  
///        

-*
for CannedExample in K3surfaceD10S9L3
 Example
   kk=ZZ/nextPrime 10^3;
   P4=kk[x_0..x_4];
   X=K3surfaceD10S9L3 P4;
   (d,sg)=(degree X, sectionalGenus X)
   minimalBetti X
   OX=sheaf(P4^1/X);
   apply(3,i->HH^i(OX))
   Ksquare(degree X,sectionalGenus X,2)
   LeBarzN6(10,9,2)
   HdotK(10,9)
  Text
   X is non-minimal with no exceptional line and three exceptional conics.
  Example
   betti(X5=ideal (gens X)_{0..5})
   betti(plane=X5:X)
   dim plane == 3
   dim  (plane+X), degree radical (plane+X)
   tally apply(primaryDecomposition (plane+X),c->(dim c, degree radical c))
*-
doc ///
Key
 K3surfaceD10S9L3
 (K3surfaceD10S9L3, PolynomialRing)
Headline
 construct a K3 surface of degree 10 and sectional genus 9 with three 6-secant line
Usage
 X=K3surfaceD10S9L3 P4
Inputs
 P4:PolynomialRing
  coordinate ring of P4
Outputs
 X:Ideal
  of a K3 surface of degree 9
Description
  Text
   We construct an K3 surface of degree 10 and sectional genus 9
  CannedExample
    i2 :    kk=ZZ/nextPrime 10^3;
    i3 :    P4=kk[x_0..x_4];
    i4 :    X=K3surfaceD10S9L3 P4;

    o4 : Ideal of P4
    i5 :    (d,sg)=(degree X, sectionalGenus X)

    o5 = (10, 9)
    o5 : Sequence
    i6 :    minimalBetti X

                0 1  2 3 4
    o6 = total: 1 9 15 9 2
             0: 1 .  . . .
             1: . .  . . .
             2: . .  . . .
             3: . 2  . . .
             4: . 4  7 2 .
             5: . 3  8 7 2
    o6 : BettiTally
    i7 :    OX=sheaf(P4^1/X);
    i8 :    apply(3,i->HH^i(OX))

            1       1
    o8 = {kk , 0, kk }
    o8 : List
    i9 : Ksquare(degree X,sectionalGenus X,2)

    o9 = -3
    i10 :    LeBarzN6(10,9,2)

    o10 = 3
    i11 :    HdotK(10,9)

    o11 = 6
  Text
   X is non-minimal with no exceptional line and three exceptional conics.
  CannedExample
    i12 :    betti(X5=ideal (gens X)_{0..5})

                 0 1
    o12 = total: 1 6
              0: 1 .
              1: . .
              2: . .
              3: . 2
              4: . 4
    o12 : BettiTally
    i13 :    betti(plane=X5:X)

                 0 1
    o13 = total: 1 2
              0: 1 2
    o13 : BettiTally
    i14 :    dim plane == 3

    o14 = true
    i15 :    dim  (plane+X), degree radical (plane+X)

    o15 = (2, 4)
    o15 : Sequence
    i16 :    tally apply(primaryDecomposition (plane+X),c->(dim c, degree radical c))

    o16 = Tally{(1, 1) => 1}
                (1, 2) => 1
                (2, 4) => 1
    o16 : Tally
  Text
   The plane intersects X in a quartic curve and three points. The three lines through
   two of these points are the thee 6-secant lines.
References
   \textit{Ranestad, K} On smooth surfaces of degree ten in the projective fourspace, Thesis, Univ of Oslo, (1988) 
SeeAlso

///
-*
for CannedExample of K3surfaceD11S11n
 Example
   kk=ZZ/nextPrime 10^3;
   P4=kk[x_0..x_4];
   X=K3surfaceD11S11Ln(P4,0);
   (d,sg)=(degree X, sectionalGenus X)
   minimalBetti X
   --OX=sheaf(P4^1/X);
   --apply(3,i->HH^i(OX))
  Text
   X has no 6-secant line, since the ideal is generated by quintics.
  Example
   X=K3surfaceD11S11Ln(P4,1);
   minimalBetti X
  Text
   In case n=1 there is precisely one 6-secant line:
  Example
   betti(X5=ideal (gens X)_{0..8})
   betti(line=X5:X)
   dim line, degree line, degree (line+X)
  Text
   In case n=2 there are two 6-secant lines:
  Example
   X=K3surfaceD11S11Ln(P4,2);
   minimalBetti X
   betti(X5=ideal (gens X)_{0..8})
   betti(residual=X5:X)
   dim residual, degree residual, degree (residual+X)
  Text
   In case n=3 there are three 6-secant lines:
  Example
   X=K3surfaceD11S11Ln(P4,3);
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
*-
doc///
Key
 K3surfaceD11S11Ln
 (K3surfaceD11S11Ln, PolynomialRing,ZZ)
Headline
 construct a K3 surface of degree 11, sectional genus 11 and precisely n 6-secants lines (4 families)
Usage
 X=K3surfaceD11S11Ln(P4,n)
Inputs
 P4:PolynomialRing
  coordinate ring of P4
 n: ZZ
   the number of desired six secant lines
Outputs
 X:Ideal
  of a K3 surface of degree 11, sectional genus 11 and precisely 'n' 6-secants lines
Description
  Text
   We construct an K3 surfaces of degree 11, sectional genus 11 and n 6-secants lines
  CannedExample
    i2 :    kk=ZZ/nextPrime 10^3;
    i3 :    P4=kk[x_0..x_4];
    i4 :    X=K3surfaceD11S11Ln(P4,0);

    o4 : Ideal of P4
    i5 :    (d,sg)=(degree X, sectionalGenus X)

    o5 = (11, 11)
    o5 : Sequence
    i6 :    minimalBetti X

                0 1  2 3 4
    o6 = total: 1 9 13 7 2
             0: 1 .  . . .
             1: . .  . . .
             2: . .  . . .
             3: . .  . . .
             4: . 9  8 . .
             5: . .  5 7 2
    o6 : BettiTally
  Text
   X has no 6-secant line, since the ideal is generated by quintics.
  CannedExample  
    i7 :    X=K3surfaceD11S11Ln(P4,1);

    o7 : Ideal of P4
    i8 :    minimalBetti X

                0  1  2 3 4
    o8 = total: 1 10 15 8 2
             0: 1  .  . . .
             1: .  .  . . .
             2: .  .  . . .
             3: .  .  . . .
             4: .  9  9 1 .
             5: .  1  6 7 2
    o8 : BettiTally
  Text
   In case n=1 there is precisely one 6-secant line:
  CannedExample    
    i9 :    betti(X5=ideal (gens X)_{0..8})

                0 1
    o9 = total: 1 9
             0: 1 .
             1: . .
             2: . .
             3: . .
             4: . 9
    o9 : BettiTally
   i10 :    betti(line=X5:X)

                0 1
   o10 = total: 1 3
             0: 1 3
   o10 : BettiTally
   i11 :    dim line, degree line, degree (line+X)

   o11 = (2, 1, 6)
   o11 : Sequence
  Text
   In case n=2 there are two 6-secant lines:
  CannedExample   
   i12 :    X=K3surfaceD11S11Ln(P4,2);
   
   o12 : Ideal of P4
   i13 : minimalBetti X
                0  1  2 3 4
   o13 = total: 1 11 17 9 2
             0: 1  .  . . .
             1: .  .  . . .
             2: .  .  . . .
             3: .  .  . . .
             4: .  9 10 2 .
             5: .  2  7 7 2
   o13 : BettiTally
   i14 : betti(X5=ideal (gens X)_{0..8})
                0 1
   o14 = total: 1 9
             0: 1 .
             1: . .
             2: . .
             3: . .
             4: . 9
   o14 : BettiTally
   i15 : betti(residual=X5:X)
                0 1
   o15 = total: 1 5
             0: 1 1
             1: . 4
   o15 : BettiTally
   i16 :  dim residual, degree residual, degree (residual+X)

   o16 = (2, 2, 12)
   o16 : Sequence
  Text
   In case n=3 there are three 6-secant lines:
  CannedExample   
   i17 :    X=K3surfaceD11S11Ln(P4,3);
   
   o17 : Ideal of P4
   i18 : minimalBetti X
                0  1  2  3 4
   o18 = total: 1 12 19 10 2
             0: 1  .  .  . .
             1: .  .  .  . .
             2: .  .  .  . .
             3: .  .  .  . .
             4: .  9 11  3 .
             5: .  3  8  7 2
   o18 : BettiTally
   i19 :    betti(X5=ideal (gens X)_{0..8})

                0 1
   o19 = total: 1 9
             0: 1 .
             1: . .
             2: . .
             3: . .
             4: . 9
   o19 : BettiTally
   i20 :    betti(plane=X5:X)

                0 1
   o20 = total: 1 2
             0: 1 2
   o20 : BettiTally
   i21 :    dim plane, degree (plane+X)

   o21 = (3, 4)
   o21 : Sequence
   i22 :    tally apply(primaryDecomposition(plane+X),c->(dim c, degree radical(c+X)))

   o22 = Tally{(1, 1) => 3}
               (2, 4) => 1

   o22 : Tally
  Text
   So the plane intersects X in a plane quartic and 3 points.
   The three 6-secant lines are the lines in the plane joining 2 of the three points.
  CannedExample   
   i23 :    Ksquare(11,11,2)

   o23 = -5
   i24 :    LeBarzN6(11,11,2)

   o24 = 4
   i25 :    HdotK(11,11)

   o25 = 9
  Text
   Summary: X is a K3 surface with precisely e1=(4-n) exceptional lines and further exceptional curves
   of larger degree as in the following pattern (e1,e2,e3,..)
   (4,0,0,0,1), (3,0,2), (2,2,1), (1,4)
References
   \textit{Popescu, S.}, Surfaces of degree $\ge 11$ in the Projective Fourspace, Dissertation, Universit\"at des Saarlandes, (1993)  
SeeAlso
///
-* for CannedExample of K3surfaceD11S12
  Example
   kk=ZZ/nextPrime 10^3;
   P4=kk[x_0..x_4];
   setRandomSeed("Fix decomposition of the (-1) lines");
   X=K3surfaceD11S12 P4;
   (d,sg)=(degree X, sectionalGenus X)
   xO=chiO X
   minimalBetti X
   B=betti(T=tateResolutionOfSurface X)
   D=canonicalDivisor X;
   degree D
   selfIntersectionNumber(X,D)
   LeBarzN6(d,sg,xO)==9
   "elapsedTime cD=decompose D;";
   "tally apply(cD,c->(dim c, degree c, betti c, selfIntersectionNumber(X,c)))";
*-
doc///
Key
 K3surfaceD11S12
 (K3surfaceD11S12, PolynomialRing)
Headline
 construct a K3 surface of degree 11 and sectional genus 12 
Usage
 X=K3surfaceD11S12 P4
Inputs
 P4:PolynomialRing
  coordinate ring of P4
Outputs
 X:Ideal
  of a K3 surface of degree 11 and sectional genus 12 
Description
  Text
   We construct a K3 surface of degree 11 and sectional genus 12 
  CannedExample
    i1 : kk=ZZ/nextPrime 10^3;
    i2 : P4=kk[x_0..x_4];
    i3 : setRandomSeed("Fix decomposition of the (-1) lines");
     -- setting random seed to 9965505783353127116382897830703483859722628482389187677576459528220608
    i4 : X=K3surfaceD11S12 P4;

    o4 : Ideal of P4
    i5 : (d,sg)=(degree X, sectionalGenus X)

    o5 = (11, 12)

    o5 : Sequence
    i6 : xO=chiO X

    o6 = 2
    i7 : minimalBetti X

                0 1 2 3
    o7 = total: 1 6 7 2
         0: 1 . . .
         1: . . . .
         2: . . . .
         3: . 2 . .
         4: . 4 7 2

    o7 : BettiTally
    i8 : B=betti(T=tateResolutionOfSurface X)

                 -1  0  1  2 3 4  5  6  7
    o8 = total: 113 68 35 13 4 4 14 43 97
            -4:   1  .  .  . . .  .  .  .
            -3: 112 68 35 13 1 .  .  .  .
            -2:   .  .  .  . 3 2  .  .  .
            -1:   .  .  .  . . .  .  .  .
             0:   .  .  .  . . 2 14 43 97

    o8 : BettiTally
    i9 : D=canonicalDivisor X;

    o9 : Ideal of P4
    i10 : degree D

    o10 = 11
    i11 : selfIntersectionNumber(X,D)

    o11 = -10
    i12 : LeBarzN6(d,sg,xO)==9

    o12 = true

  Text
    X has no 6-secant line, since the ideal is generated by quintics.
    Thus there are nine (-1) lines and a (-1) conic. 
References
   \textit{Popescu, S.}, Surfaces of degree $\ge 11$ in the Projective Fourspace, Dissertation, Universit\"at des Saarlandes, (1993) 
SeeAlso
  selfIntersectionNumber
  LeBarzN6
  canonicalDivisor
  
///
-* for CannedExample K3SurfaceD12
Example
   kk=ZZ/nextPrime 10^3;
   P4=kk[x_0..x_4];
   setRandomSeed("Fix decomposition of the (-1) curves");
   X=K3surfaceD12 P4;
   (d,sg)=(degree X, sectionalGenus X)
   xO=chiO X
   minimalBetti X
   B=betti(T=tateResolutionOfSurface X)
   D=canonicalDivisor X;
   degree D
   selfIntersectionNumber(X,D)
   LeBarzN6(d,sg,xO)==10

*-
doc///
Key
 K3surfaceD12
 (K3surfaceD12, PolynomialRing)
Headline
 construct a K3 surface of degree 12 and sectional genus 14 
Usage
 X=K3surfaceD12 P4
Inputs
 P4:PolynomialRing
  coordinate ring of P4
Outputs
 X:Ideal
  of a K3 surface of degree 12 and sectional genus 14
Description
  Text
    We construct an K3 surfaces of degree 12 and sectional genus 14 
  CannedExample
   i1 : kk=ZZ/nextPrime 10^3;
   i2 : P4=kk[x_0..x_4];
   i3 : setRandomSeed("Fix decomposition of the (-1) curves");
   -- setting random seed to 1006516084118665838754672680901051869831985476721307955435222319012395033
   i4 : X=K3surfaceD12 P4;

   o4 : Ideal of P4
   i5 : (d,sg)=(degree X, sectionalGenus X)

   o5 = (12, 14)

   o5 : Sequence
   i6 : xO=chiO X

   o6 = 2
   i7 : minimalBetti X

               0 1  2 3
   o7 = total: 1 9 11 3
            0: 1 .  . .
            1: . .  . .
            2: . .  . .
            3: . .  . .
            4: . 9 11 3

   o7 : BettiTally
   i8 : B=betti(T=tateResolutionOfSurface X)

                -1  0  1  2 3 4 5  6  7
   o8 = total: 127 77 40 15 5 3 9 34 83
           -4:   1  .  .  . . . .  .  .
           -3: 126 77 40 15 1 . .  .  .
           -2:   .  .  .  . 4 3 .  .  .
           -1:   .  .  .  . . . .  .  .
            0:   .  .  .  . . . 9 34 83

   o8 : BettiTally
   i9 : D=canonicalDivisor X;

   o9 : Ideal of P4
   i10 : degree D

   o10 = 14
   i11 : selfIntersectionNumber(X,D)

   o11 = -11
   i12 : LeBarzN6(d,sg,xO)==10

   o12 = true

  Text
   X has no 6-secant line, since the ideal is generated by quintics.
   Thus there ten (-1) lines and one (-1) quartic. 
References
   \textit{Decker, W., Ein, L., Schreyer, F-O.}, Construction of surfaces in $\Pn 4$, J. Algebraic Geom., 2,  (1993), 185-237
SeeAlso
  selfIntersectionNumber
  LeBarzN6
  canonicalDivisor
///
-* for CannedExample in K3surfaceD13
  Example
   kk=ZZ/nextPrime 10^3;
   P4=kk[x_0..x_4];
   setRandomSeed("Fix decomposition of the (-1) curves");
   X=K3surfaceD13 P4;
   (d,sg)=(degree X, sectionalGenus X)
   xO=1+(genera X)_0
   HdotK(d,sg)
   Ksquare(d,sg,xO)
   minimalBetti X
   B=betti(T=tateResolutionOfSurface X)
   elapsedTime D=canonicalDivisor X;
   (degree D,genus D) == (17,-10)
   residual=residualInQuintics X;
   dim residual 
   LeBarzN6(d,sg,xO) == 10
   manyPts=apply(30,i->(
      pts=saturate(D+ideal random(1,P4));
      rpts=radical pts;
      assert(rpts==  pts);
   cpts=decompose pts;
   sevenPts=last cpts));
   all(manyPts,p->degree p==7)
   J7=intersect manyPts;
   E7=ideal (gens J7)_{0..6};
   minimalBetti E7
   degree E7, genus E7
   betti(D4=D:E7)
   degree D4, genus D4
   manyPts2=for i from 1 to 30 list (
      pts=saturate(D4+ideal random(1,P4));
      rpts=radical pts;
      assert(rpts==  pts);
   cpts=decompose pts;
   if degree last cpts>3 then last cpts else continue);
   betti(J1=intersect manyPts2)
   E1=ideal(gens J1)_{0..12};
   degree E1, genus E1
   D3=D4:E1
   decompose D3
   degree D3, genus D3
   comps={E1,E7,D3};
   matrix apply(comps,c->apply(comps,d->if dim(c+d)>0 then degree (c+d) else 0))
   apply(comps,c->selfIntersectionNumber(X,c))
   d1=d+2*HdotK(d,sg)+Ksquare(d,sg,xO)
   d2=d1+2*6*6-6^2
   d+2*(10+7*7)-10-49
 Text
    Since the residual scheme in quintics is empty, there are no 6-secants.
    Thus there are ten (-1)-lines and  a (-1) septic. The surface is a K3 surface blown-up
    in 11 points embedded by a linear system (Hmin;7,1^10) with Hmin^2=72. Since 22<25
    we expect that the minimal K3 surface is special, moving in a 19-3 dimensional family.
  Example
    chiHmin= 72//2+2
    chiHmin-binomial(7+1,2)-10==5-5

*-

doc///
Key
 K3surfaceD13
 (K3surfaceD13, PolynomialRing)
Headline
 construct a K3 surface of degree 13 and sectional genus 16 
Usage
 X=K3surfaceD13 P4
Inputs
 P4:PolynomialRing
  coordinate ring of P4
Outputs
 X:Ideal
  of a K3 surface of degree 13 and sectional genus 16
Description
  Text
    We construct an K3 surfaces of degree 13 and sectional genus 16. 
  CannedExample
    i1 : kk=ZZ/nextPrime 10^3;
    i2 : P4=kk[x_0..x_4];
    i3 : setRandomSeed("Fix decomposition of the (-1) curves");
    -- setting random seed to 1006516084118665838754672680901051869831985476721307955435222319012395033
    i4 : X=K3surfaceD13 P4;

    o4 : Ideal of P4
    i5 : (d,sg)=(degree X, sectionalGenus X)

    o5 = (13, 16)

    o5 : Sequence
    i6 : xO=1+(genera X)_0

    o6 = 2
    i7 : HdotK(d,sg)

    o7 = 17
    i8 : Ksquare(d,sg,xO)

    o8 = -11
    i9 : minimalBetti X

                0 1  2  3 4
    o9 = total: 1 9 16 10 2
             0: 1 .  .  . .
             1: . .  .  . .
             2: . .  .  . .
             3: . .  .  . .
             4: . 4  .  . .
             5: . 5 16 10 2

    o9 : BettiTally
    i10 : B=betti(T=tateResolutionOfSurface X)

                  -1  0  1  2 3 4 5  6  7
    o10 = total: 141 86 45 17 6 4 6 25 69
             -4:   1  .  .  . . . .  .  .
             -3: 140 86 45 17 1 . .  .  .
             -2:   .  .  .  . 5 4 .  .  .
             -1:   .  .  .  . . . 2  .  .
              0:   .  .  .  . . . 4 25 69

    o10 : BettiTally
    i11 : elapsedTime D=canonicalDivisor X;
     -- 8.82468s elapsed

    o11 : Ideal of P4
    i12 : (degree D,genus D) == (17,-10)

    o12 = true
    i13 : residual=residualInQuintics X;

    o13 : Ideal of P4
    i14 : dim residual

    o14 = 0
    i15 : LeBarzN6(d,sg,xO) == 10

    o15 = true
  Text
    Since the residual scheme in quintics is empty, there are no 6-secants.
    Thus there are ten (-1)-lines and a (-1) septic. The surface is a K3 surface blown-up
    in 11 points embedded by a linear system (Hmin;7,1^10) with Hmin^2=72. Since 22<25
    we expect that the minimal K3 surface is special, moving in a 19-3 dimensional family.
  
References
   \textit{Popescu, S.}, Surfaces of degree $\ge 11$ in the Projective Fourspace, Dissertation, Universit\"at des Saarlandes, (1993)
SeeAlso
  selfIntersectionNumber
  residualInQuintics
  LeBarzN6
  canonicalDivisor
///

-* for CannedExample in K3surfaceD14
needsPackage"NongeneralTypeSurfacesInP4"
  Example
   kk=ZZ/nextPrime 10^2;
   P4=kk[x_0..x_4];
   setRandomSeed("Fix the decomposition of the (-1) curves");
   X=K3surfaceD14 P4;
   minimalBetti X
   (d,sg)=(degree X, sectionalGenus X)
   xO=1+(genera X)_0
   B=betti(T=tateResolutionOfSurface X)
   HdotK(d,sg)==22
   Ksquare(d,sg,xO)==-15
   D=canonicalDivisor X;
   (degree D, genus D)==(22,-14)
   elapsedTime selfIntersectionNumber(X,D)==-15 
   betti(fD= res D)
   elapsedTime cD=primaryDecomposition D;
   tally apply(cD,c->(degree c, genus c, selfIntersectionNumber(X,c)))
  Text
   X is blowup of a minimal K3-surface in 15 points embedded by
   .  
   
  Example  
   D=canonicalDivisor X;
   degree D, genus D
   elapsedTime selfIntersectionNumber(X,D)==-15  
   elapsedTime cD=decompose D;
   tally apply(cD,c->(degree c, genus c, selfIntersectionNumber(X,c)))
   
   residual=residualInQuintics X;
   dim residual, degree residual
   cResidual=primaryDecomposition residual;
   tally apply(cResidual,c->(dim c, degree c, degree radical c, dim(c+X), degree(c+X), degree radical(c+X)))
  Text

*-
doc///
Key
 K3surfaceD14
 (K3surfaceD14, PolynomialRing)
Headline
 construct a K3 surface of degree 14 and sectional genus 19 
Usage
 X=K3surfaceD14 P4
Inputs
 P4:PolynomialRing
  coordinate ring of P4
Outputs
 X:Ideal
  of a K3 surface of degree 14 and sectional genus 19
Description
  Text
   We construct an K3 surfaces of degree 14 and sectional genus 19
  CannedExample
   i1 : kk=ZZ/nextPrime 10^3;
   i2 : P4=kk[x_0..x_4];
   i3 : setRandomSeed("Fix decomposition of the (-1) curves");
   -- setting random seed to 1006516084118665838754672680901051869831985476721307955435222319012395033
   i4 : X=K3surfaceD14 P4;

   o4 : Ideal of P4
   i5 : (d,sg)=(degree X, sectionalGenus X)

   o5 = (14, 19)

   o5 : Sequence
   i6 : xO=chiO X

   o6 = 2
   i7 : minimalBetti X

               0 1  2 3
   o7 = total: 1 8 10 3
            0: 1 .  . .
            1: . .  . .
            2: . .  . .
            3: . .  . .
            4: . 4  2 .
            5: . 4  8 3

   o7 : BettiTally
   i8 : B=betti(T=tateResolutionOfSurface X)

                -1  0  1  2 3 4 5  6  7
   o8 = total: 159 98 52 20 8 7 7 22 62
           -4:   1  .  .  . . . .  .  .
           -3: 158 98 52 20 1 . .  .  .
           -2:   .  .  .  . 7 7 3  .  .
           -1:   .  .  .  . . . .  .  .
            0:   .  .  .  . . . 4 22 62

   o8 : BettiTally
   i9 : D=canonicalDivisor X;

   o9 : Ideal of P4
   i10 : degree D

   o10 = 22
   i11 : elapsedTime selfIntersectionNumber(X,D)==-15
     -- 29.9454s elapsed

   o11 = true
   i12 : residual=residualInQuintics X;

   o12 : Ideal of P4
   i13 : dim residual, degree residual

   o13 = (3, 4)

   o13 : Sequence
   i14 : cResidual=primaryDecomposition residual;
   i15 : tally apply(cResidual,c->(dim c, degree c, degree radical c, dim(c+X), degree(c+X), degree radical(c+X)))

   o15 = Tally{(3, 1, 1, 2, 6, 6) => 4}

   o15 : Tally
   i16 : cResidual



   o16 : List
  Text
    There are 4 planes containing a plane sextic curve. Any line in one of
    the planes is a 6-secant line, and Le Barz secant formula does not apply.
   
   
References
   \textit{Popescu, S.}, Surfaces of degree $\ge 11$ in the Projective Fourspace, Dissertation, Universit\"at des Saarlandes, (1993)  
SeeAlso
  selfIntersectionNumber
  residualInQuintics
  LeBarzN6
  canonicalDivisor
///
-* for CannedExample searchHmBundle 
    kk=ZZ/2;
    E=kk[e_0..e_4,SkewCommutative=>true];
    c=10;
    setRandomSeed("do 2^c cases");
    elapsedTime Ms=searchHMBundle(E,c) -- 11.3592s elapsed
    11.3592*2^(20-c)/60/60
*-

doc///
Key
 searchHMBundle
 (searchHMBundle,Ring,ZZ)
Headline
 search a Horrocks-Mumford bundle on P4
Usage
 Ms=searchHMBundle(E,c)
Inputs
 E:Ring
  exterior algebra dual to the coordinate ring of P4
 c:ZZ
  search for example up to codim c
Outputs
 Ms:List
   of 2x5 matries with quadratic entries in E
Description
  Text
    Choosing randomly 3x2 matrices with entries of degree 2,
    we check whether its syzygy matrix contains a 2x5 matrix leading to the
    desired monad.
  CannedExample
    i1 : kk=ZZ/2;
    i2 : E=kk[e_0..e_4,SkewCommutative=>true];
    i3 : c=10;
    i4 : setRandomSeed("do 2^c cases");
     -- setting random seed to 1127965201797969169793845
    i5 : elapsedTime Ms=searchHMBundle(E,c) -- 11.3592s elapsed
     -- 11.8393s elapsed
       number of trials = 2221
       (N,M) = (1024, 35)

    o5 = {}

    o5 : List
    i6 : 11.3592*2^(20-c)/60/60

    o6 = 3.231061333333333

    o6 : RR (of precision 53)
    
  Text
    There are 2*(5-3)+8+3+24 dimansional family of 3x2 submatices of the 5x2
    Horrocks-Mumford matrix compared to 3*2*10-1 dimenensional family of all matrices.
    So the codimsion is
    20=3*2*10-1-(2*(5-3)+8+3+24)
    Thus the runnig time to find an example is about 3.5 hours
    over ZZ/2.
SeeAlso
  horrocksMumfordSurface
  varietyOfUnstablePlanes
///
-* for CannedExample in varietyOfUnstablePlanes
  Example
    kk=ZZ/2;
    E=kk[e_0..e_4,SkewCommutative=>true];
  Text
    The following matrix was found using searchHMBundle.
  Example
    m2x5=matrix {{e_0*e_1+e_1*e_2+e_2*e_3+e_0*e_4+e_1*e_4+e_3*e_4,
      e_0*e_2+e_1*e_3+e_2*e_3+e_0*e_4+e_2*e_4+e_3*e_4,
      e_0*e_3+e_1*e_3+e_2*e_3+e_0*e_4+e_2*e_4,
      e_1*e_2+e_0*e_3+e_1*e_3+e_2*e_4, e_0*e_3+e_2*e_3+e_0*e_4},
      {e_1*e_4+e_3*e_4, e_0*e_4+e_1*e_4,
      e_1*e_2+e_1*e_4+e_2*e_4+e_3*e_4,
      e_0*e_2+e_1*e_3+e_0*e_4+e_1*e_4,
      e_0*e_1+e_1*e_3+e_2*e_3+e_0*e_4+e_1*e_4+e_2*e_4+e_3*e_4}};
  Text
    It defines a vector bundle defined over ZZ/2 since its Tate resolution
    has the right shape.
  Example
    T=res(coker m2x5,LengthLimit=>5);
    betti (T'= res(coker transpose T.dd_5**E^{2},LengthLimit=>10)[5])
  Text
    Its variety of unstable is as expected.
  Example
    pentagons=varietyOfUnstablePlanes(m2x5,Verbose=>2);	 
    fiveLines=pentagons_0;
    betti res (pent_0=intersect(fiveLines))
    betti res (pent_1=intersect(pentagons_1))
    fivePoints=pent_0+pent_1;
    (dim fivePoints,degree fivePoints) == (1,5)
    betti res fivePoints

*-


doc///
Key
 varietyOfUnstablePlanes
 (varietyOfUnstablePlanes,Matrix)
 [varietyOfUnstablePlanes,Verbose]
Headline
 investigate the variety of unstable planes of the bundle corresponding m2x5
Usage
 pentagons=varietyOfUnstablePlanes(m2x5)
Inputs
 m2x5:Matrix
  2x5 matrix with entries of degree in an exterior algebra dual to the coordinate ring of P4
Outputs
 pentagons:List
   list of pentagons
Description
  Text
    The matrix m2x5 defines a vector bundle of rank 2 and chern polynomial
    1-t+4t^2. The functions computes partial information about the variety
    of unstable planes, which following [BHM] is the interesction of a
    the Grassmannian G(2,5) with a P1xP4 in P9. By [DS] this variety should coincide with
    Shioda's modular variety. We verify some of the assertians. In particular,
    that the singular fibers are 12 pentagons, which come in pairs.
  
  CannedExample
    i1 : kk=ZZ/2;
    i2 : E=kk[e_0..e_4,SkewCommutative=>true];
  Text
    The following matrix was found using searchHMBundle.
  CannedExample
    i3 : m2x5=matrix {{e_0*e_1+e_1*e_2+e_2*e_3+e_0*e_4+e_1*e_4+e_3*e_4,
              e_0*e_2+e_1*e_3+e_2*e_3+e_0*e_4+e_2*e_4+e_3*e_4,
	      e_0*e_3+e_1*e_3+e_2*e_3+e_0*e_4+e_2*e_4,
	      e_1*e_2+e_0*e_3+e_1*e_3+e_2*e_4, e_0*e_3+e_2*e_3+e_0*e_4},
	  {e_1*e_4+e_3*e_4, e_0*e_4+e_1*e_4,
	      e_1*e_2+e_1*e_4+e_2*e_4+e_3*e_4,
	      e_0*e_2+e_1*e_3+e_0*e_4+e_1*e_4,
	      e_0*e_1+e_1*e_3+e_2*e_3+e_0*e_4+e_1*e_4+e_2*e_4+e_3*e_4}};

                  2      5
    o3 : Matrix E  <-- E
  Text
    It defines a vector bundle defined over ZZ/2 since its Tate resolution has the right shape.
  CannedExample
    i4 : T=res(coker m2x5,LengthLimit=>5);
    i5 : betti (T'= res(coker transpose T.dd_5**E^{2},LengthLimit=>10)[5])

                 -5 -4 -3 -2 -1 0 1  2  3  4   5
    o5 = total: 100 37 14 10  5 2 5 10 14 37 100
            -4: 100 35  4  .  . . .  .  .  .   .
	    -3:   .  2 10 10  5 . .  .  .  .   .
	    -2:   .  .  .  .  . 2 .  .  .  .   .
	    -1:   .  .  .  .  . . 5 10 10  2   .
	     0:   .  .  .  .  . . .  .  4 35 100

    o5 : BettiTally
  Text
    Its variety of unstable is as expected.
  CannedExample
    i6 : pentagons=varietyOfUnstablePlanes(m2x5,Verbose=>2);
                                   2          2   4      3    4   4    3     2 2      3    4
      singularFibers = (t)(s + t)(s  + s*t + t )(s  + s*t  + t )(s  + s t + s t  + s*t  + t )
      -- 5.26706s elapsed
      number of components and intersection matrices = Tally{(5, | -2 1  0  0  1  |) => 12}
                                                                 | 1  -2 1  0  0  |
								 | 0  1  -2 1  0  |
								 | 0  0  1  -2 1  |
								 | 1  0  0  1  -2 |
       -- => the singular fibers consists of 12 pentagons of lines.
       -- => the surface of unstable plane of the bundle coincides with Shioda's modular surface
       -- => the bundle is projectively equivalent to the HM bundle
                                                                 0  1  2  3 4
      number and betti table of singular points = Tally{(5, total: 1 10 20 15 4) => 12}
                                                              0: 1  .  .  . .
                                                              1: . 10 20 15 4
      pairs of singular fibers = {{0, 1}, {2, 4}, {3, 7}, {5, 11}, {6, 10}, {8, 9}}
    i7 : fiveLines=pentagons_0;
    i8 : betti res (pent_0=intersect(fiveLines))

                0 1 2 3
    o8 = total: 1 5 5 1
             0: 1 . . .
	     1: . 5 5 .
	     2: . . . 1

    o8 : BettiTally
    i9 : betti res (pent_1=intersect(pentagons_1))

                0 1 2 3
    o9 = total: 1 5 5 1
             0: 1 . . .
	     1: . 5 5 .
	     2: . . . 1

    o9 : BettiTally
    i10 : fivePoints=pent_0+pent_1;

    o10 : Ideal of GF 256[x ..x ]
    0   4
    i11 : (dim fivePoints,degree fivePoints) == (1,5)

    o11 = true
    i12 : betti res fivePoints

                 0  1  2  3 4
    o12 = total: 1 10 20 15 4
              0: 1  .  .  . .
	      1: . 10 20 15 4

    o12 : BettiTally
   
  Text
    This function is incomplete. Ideally we would like to compute a coordinate change
    of P4 and and basis change of source and target of the 2x5 matrix which moves
    the matrix to the Horrocks Mumford matrix.
    
SeeAlso
  horrocksMumfordSurface
  searchHMBundle
///

///
pts=apply(decompose fivePoints, c->syz transpose jacobian c)
aut=pts_0|pts_1|pts_2|pts_3|pts_4
kk'=coefficientRing ring aut
aut=sub(aut,kk')
E'=kk'[gens E,SkewCommutative=>true]
m2x5'=sub(m2x5,E')
apply(5,i->(
entry=(m2x5'*inverse aut)_(1,i);
betti syz(map(E'^1,,entry*vars E'),DegreeLimit=>3)))


///


///
    kk=ZZ/2;
    E=kk[e_0..e_4,SkewCommutative=>true];
    c=21;
    setRandomSeed("second time do 2^c cases once more");
    elapsedTime Ms=searchHMBundle(E,c);#Ms
    

///

  

/// -* Test unstable planes *-
restart
needsPackage "NongeneralTypeSurfacesInP4"

kk=ZZ/2;
    E=kk[e_0..e_4,SkewCommutative=>true];
Ms={matrix {{e_0*e_1+e_1*e_2+e_2*e_3+e_0*e_4+e_1*e_4+e_2*e_4,
      e_0*e_2+e_1*e_3+e_2*e_3+e_0*e_4, e_1*e_3+e_2*e_4,
      e_0*e_3+e_2*e_3, e_1*e_2+e_0*e_3+e_0*e_4+e_1*e_4},
      {e_1*e_4+e_2*e_4, e_1*e_3+e_2*e_4+e_3*e_4,
      e_1*e_2+e_0*e_3+e_2*e_3+e_1*e_4+e_2*e_4+e_3*e_4,
      e_0*e_2+e_0*e_3+e_1*e_3+e_2*e_3+e_0*e_4+e_3*e_4,
      e_0*e_1+e_1*e_3+e_2*e_3+e_2*e_4}},
 matrix {{e_1*e_2+e_2*e_3+e_0*e_4+e_1*e_4+e_3*e_4,
      e_0*e_1+e_1*e_3+e_2*e_3+e_3*e_4, e_0*e_2+e_0*e_3+e_2*e_4,
      e_1*e_3+e_0*e_4+e_1*e_4, e_2*e_3+e_0*e_4+e_2*e_4},
      {e_0*e_3+e_1*e_3+e_0*e_4+e_1*e_4+e_2*e_4+e_3*e_4,
      e_1*e_2+e_2*e_3, e_1*e_2+e_0*e_3+e_2*e_3+e_1*e_4,
      e_0*e_2+e_1*e_2+e_1*e_3+e_2*e_3+e_1*e_4+e_2*e_4,
      e_0*e_1+e_1*e_2+e_0*e_3+e_1*e_3+e_2*e_3+e_0*e_4+e_2*e_4}},
 matrix {{e_0*e_1+e_1*e_2+e_2*e_3+e_0*e_4+e_1*e_4+e_3*e_4,
      e_0*e_2+e_1*e_3+e_2*e_3+e_0*e_4+e_2*e_4+e_3*e_4,
      e_0*e_3+e_1*e_3+e_2*e_3+e_0*e_4+e_2*e_4,
      e_1*e_2+e_0*e_3+e_1*e_3+e_2*e_4, e_0*e_3+e_2*e_3+e_0*e_4},
      {e_1*e_4+e_3*e_4, e_0*e_4+e_1*e_4,
      e_1*e_2+e_1*e_4+e_2*e_4+e_3*e_4,
      e_0*e_2+e_1*e_3+e_0*e_4+e_1*e_4,
      e_0*e_1+e_1*e_3+e_2*e_3+e_0*e_4+e_1*e_4+e_2*e_4+e_3*e_4}},
 matrix {{e_0*e_1+e_0*e_3+e_2*e_3+e_1*e_4+e_3*e_4, e_0*e_2+e_1*e_2+e_1*e_3+e_1*e_4+e_2*e_4,
      e_1*e_3+e_2*e_3+e_0*e_4+e_1*e_4+e_2*e_4, e_1*e_2+e_0*e_3+e_2*e_3+e_0*e_4+e_1*e_4+e_3*e_4,
      e_1*e_2+e_2*e_3+e_3*e_4}, {e_1*e_4+e_2*e_4+e_3*e_4, e_1*e_3+e_2*e_4,
      e_0*e_3+e_1*e_3+e_3*e_4, e_0*e_2+e_1*e_2+e_1*e_3+e_2*e_3+e_0*e_4+e_2*e_4+e_3*e_4,
      e_0*e_1+e_1*e_2+e_1*e_4}},
matrix {{e_0*e_1+e_0*e_3+e_2*e_3+e_1*e_4+e_3*e_4, e_0*e_2+e_1*e_2+e_1*e_3+e_1*e_4+e_2*e_4,
     e_1*e_3+e_2*e_3+e_0*e_4+e_1*e_4+e_2*e_4, e_1*e_2+e_0*e_3+e_2*e_3+e_0*e_4+e_1*e_4+e_3*e_4,
     e_1*e_2+e_2*e_3+e_3*e_4}, {e_1*e_4+e_2*e_4+e_3*e_4, e_1*e_3+e_2*e_4,
     e_0*e_3+e_1*e_3+e_3*e_4, e_0*e_2+e_1*e_2+e_1*e_3+e_2*e_3+e_0*e_4+e_2*e_4+e_3*e_4,
     e_0*e_1+e_1*e_2+e_1*e_4}}
}
-- 6819.37s elapsed for c=20 one example
 -- 23703.1s elapsed for c=21 none found
log_2 570802
 
betti(m2x5=Ms_2)
betti(T=res(coker m2x5,LengthLimit=>5))
betti (THM= res(coker transpose T.dd_5**E^{2},LengthLimit=>10)[5])
basis(2,E)
pentagons=varietyOfUnstablePlanes(m2x5,Verbose=>2);


///

///   
st=(vars P1xP4')_{0,1}
diff(transpose st, gens sum csingFibs_rows)
cc=sortedComponents_2
    qs=apply(4,i->syz transpose jacobian trim(cc_i+cc_(i+1)))|{syz transpose jacobian trim(cc_4+cc_0)};
m=sub((qs_0|qs_1|qs_2|qs_3|qs_4),kk')
vars P4'*m
transpose inverse m == inverse transpose m
    possible={transpose inverse m,transpose  m,inverse m,m}
standardRow=ideal(E'_0*E'_2,E'_1*E'_3,E'_2*E'_4,E'_3*E'_0,E'_4*E'_1)
standardRow1=ideal(E'_0*E'_1,E'_1*E'_2,E'_2*E'_3,E'_3*E'_4,E'_4*E'_0)
standardRow2=ideal(E'_0*E'_3,E'_1*E'_4,E'_2*E'_0,E'_3*E'_1,E'_4*E'_2)
singFibers_1

trim sub(singFibers_0,vars P4'*transpose m)
trim sub(singFibers_1,vars P4'*transpose m)
trim sub(singFibers_2,vars P4'*transpose m)
trim sub(singFibers_7,vars P4'*transpose m)
decompose trim sub(singFibers_2,vars P4'*transpose m)

tally apply(possible, m1->(autP4=vars E'*m1;
	(sub(standardRow2,autP4)==ideal(sub(m2x5^{0},E')),
	    standardRow2==ideal(sub(m2x5^{0},autP4)),
	    standardRow2,ideal(sub(m2x5^{1},autP4)),
	    sub(standardRow2,autP4)==ideal(sub(m2x5^{1},E')),
	    sub(standardRow2,autP4)==ideal(sub(m2x5^{1}+m2x5^{0},E')),
	    betti sub(standardRow2,autP4),betti ideal(sub(m2x5^{1}+m2x5^{0},E')))
	)
    )
netList apply(possible, m1->(autP4=vars E'*m1;trim ideal sub(m2x5^{1}+m2x5^{0},autP4)))
)))
basis(2,E)
vars P
m5x5
kk''=GF(2,4)
P'=kk''[gens P]
E''=kk''[gens E,SkewCommutative=>true]
EP'=E''**P'
coefficientRing E'
J'=sub(J,EP')
m5x2E
m2x5P'=sub((sub(m2x5,EP')%J'),P')
m5x5
row0=m2x5P'^{0}
row1=m2x5P'^{1}
betti(ideal row1 +sub(pfaffians(4,m5x5),P'))
tally apply(decompose (ideal row1 +sub(pfaffians(4,m5x5),P')),c->betti c)
betti(ideal (row0+row1) +sub(pfaffians(4,m5x5),P'))
tally apply(decompose (ideal(row0+row1) +sub(pfaffians(4,m5x5),P')),c->betti c)


oE3=matrix{apply(5,i->E'_i*E'_((i+1)%5)*E'_((i+2)%5))}
as=apply(5,i->transpose syz transpose syz(map(E'^1,,oE3_{i}*sub(sub(m2x5^{0},E'),autP4)),DegreeLimit=>5))
n=sub(as_0||as_1||as_2||as_3||as_4,kk')
inverse n
pos2={n,inverse n, transpose n, transpose inverse n}
apply(possible,m1->(autP4=vars E'*m1;apply(pos2,n1->sub(standardRow,autP4)==ideal(sub(m2x5^{0},E')*n1))))


///

    -* Test section *-

TEST /// -* tateResolutionOfSurface and chiITable *-
kk=ZZ/nextPrime 10^2
P4=kk[x_0..x_4]
minimalBetti(X=K3surfaceD13 P4)
(d,sg)=(degree X,sectionalGenus X)
elapsedTime b1=betti tateResolutionOfSurface(X,7)
b2=chiITable(d,sg,2)
assert(values(b1-b2)=={0})
///

TEST /// -* adjunctionProcess, (-1)-lines, 6-secants and LeBarzN6 
           on Schreyer surface *-
kk=ZZ/3
P4=kk[x_0..x_4]
elapsedTime minimalBetti(X=specificSchreyerSurface(P4,1))
elapsedTime L=adjunctionProcess(X,1);
L_0
X1=L_3;
(n1,d1,sg1)=(numgens ring X1-1,degree X1, sectionalGenus X1)
assert((L_0)_2==(n1,d1,sg1))
R=residualInQuintics X;
assert(all(decompose R,c->(dim c==2 and 6*degree c==degree (c+X))))
assert(degree R + (L_0)_1==LeBarzN6(degree X, sectionalGenus X,1))
///

TEST /// -* canonical divisor on Abo surface, HdotK, selfIntersectionNumber, 
           partitionOfCanonicalDivisorOfAboSurface *-
kk=ZZ/19
P4=kk[x_0..x_4]
E=kk[e_0..e_4,SkewCommutative=>true]
setRandomSeed("fairly fast, about 12 seconds");
elapsedTime X=specificAboSurface(P4,E,0,Verbose=>true);
elapsedTime K=canonicalDivisor X;
(d,sg)=(degree X, sectionalGenus X)
assert(degree K==HdotK(d,sg))
elapsedTime cK=decompose K;
assert(all(cK,c->(-genus c+1== -selfIntersectionNumber(X,c))))
elapsedTime assert(partitionOfCanonicalDivisorOfAboSurface X == {1,2,2,2,2,3})
///

end--

-* Development section *-

restart
needsPackage "NongeneralTypeSurfacesInP4"

elapsedTime installPackage "NongeneralTypeSurfacesInP4"

viewHelp "NongeneralTypeSurfacesInP4"

check "NongeneralTypeSurfacesInP4"


kk=ZZ/19
P4=kk[x_0..x_4]
E=kk[e_0..e_4,SkewCommutative=>true]
X=specificAboSurface(P4,E,6,Verbose=>true);
minimalBetti X
betti(T=tateResolutionOfSurface(X))
ci=ideal(gens X*random(source gens X,P4^{-5,-5}));
minimalBetti (Y=ci:X)
betti(TY=tateResolutionOfSurface(Y,8))
(d,sg)=(degree Y, sectionalGenus Y)
chiITable(d+1,sg,2)
chiITable(15,14,-2)
elapsedTime betti (T1=res(coker random(E^{3:1,3:0},E^{5:-1,2:-2}),LengthLimit=>6))
betti(T2=res(coker transpose T1.dd_3,LengthLimit=>8))
3*1-(5*4+2*6)+15*4-23
-(3*1+3*4)+(5*6+2*4)-15


-* problem 9.5 rational surface of degree 14 *-
kk=ZZ/2
E=kk[e_0..e_4,SkewCommutative=>true]
needsPackage "NongeneralTypeSurfacesInP4"
chiITable(14,18,1)
k2=Ksquare(14,18,1)
2*(-k2+9)-35
LeBarzN6(14,1
sv=syz vars E
mats1={
matrix {{e_0+e_1+e_4, e_0+e_3, e_1+e_3+e_4, e_2+e_3, e_0+e_2, e_1+e_3+e_4, e_1+e_2+e_3}, {e_0+e_3, e_3, e_0+e_4, e_3+e_4, e_1+e_2+e_4, e_0+e_1+e_2+e_3+e_4, e_0}, {e_2, e_2, e_2+e_3, e_0+e_2, e_0+e_1+e_2+e_3, e_1+e_4, e_0+e_2+e_3+e_4}, {e_1+e_3+e_4, e_0+e_1+e_3+e_4, e_0+e_2+e_3, e_0+e_1+e_3+e_4, e_2+e_3, e_0+e_1+e_4, e_0+e_2+e_4}, {e_0+e_3+e_4, e_3, e_0+e_1, e_1+e_3, e_1+e_4, e_0+e_1+e_2+e_3, e_2+e_3}, {e_0+e_2, e_1, e_1+e_2, e_2, e_1+e_2+e_4, e_1+e_2+e_3+e_4, e_0}},
matrix {{e_0+e_1+e_2+e_4, e_0+e_1+e_2+e_4, e_0+e_1+e_4, e_2+e_3+e_4, e_2+e_4, e_4, e_3+e_4}, {e_0+e_1+e_3, e_0+e_2+e_4, e_0+e_1+e_2+e_3, 0, e_1+e_2+e_4, e_1+e_2+e_3, e_1+e_2}, {e_0, e_0+e_1+e_3, e_1+e_2+e_3+e_4, e_0+e_2, e_0+e_1+e_4, e_1+e_4, e_1+e_2+e_3}, {e_1+e_3, e_2+e_3+e_4, e_1+e_2+e_4, e_0+e_3+e_4, 0, e_1, e_0+e_2+e_3}, {e_0+e_4, e_0+e_1+e_3+e_4, e_0+e_2+e_3, e_0+e_3+e_4, e_0+e_1+e_2+e_4, e_0+e_2, e_0+e_4}, {0, e_0+e_1+e_4, e_0+e_1+e_2+e_4, e_0+e_2+e_3, e_1+e_2, e_2+e_3, e_1+e_3+e_4}},
matrix {{e_1+e_3, e_0+e_3, e_0, e_1+e_3+e_4, e_0+e_1+e_2+e_4, e_0+e_2+e_4, e_2+e_3+e_4}, {e_0+e_1+e_2+e_3+e_4, e_1+e_2+e_3+e_4, e_3, e_0+e_1+e_2, e_0+e_2+e_4, e_1+e_2+e_3+e_4, e_1+e_2+e_4}, {e_1+e_3, e_1+e_2+e_4, 0, e_1+e_3+e_4, e_0+e_1+e_2+e_3+e_4, e_0+e_1+e_3, e_0+e_1}, {e_0+e_1+e_2+e_3+e_4, e_0+e_1+e_3, e_1+e_3, e_0+e_2+e_3+e_4, e_2+e_3, e_1+e_2+e_4, e_0}, {e_1+e_3, e_1+e_2+e_4, 0, e_0+e_2+e_3, e_0+e_1+e_2+e_4, e_0+e_1+e_3, e_0+e_1}, {e_1+e_2+e_3, e_1+e_4, e_2+e_3+e_4, e_1+e_2+e_4, e_0+e_4, e_0+e_1+e_2+e_3, e_1+e_2+e_3}},
matrix {{e_1+e_2+e_3, e_0+e_1+e_2, e_4, e_1+e_2+e_3+e_4, e_0+e_2+e_3, e_1+e_3+e_4, e_0+e_1+e_3+e_4}, {e_0+e_1+e_2+e_3, e_0+e_1+e_2+e_3, 0, e_0+e_1+e_2+e_3, e_2+e_3, e_0+e_2+e_3, e_0}, {e_0+e_1+e_2+e_3, e_0+e_1+e_2+e_3, e_2+e_3, e_0+e_1+e_2+e_3, e_0+e_1+e_3+e_4, e_1+e_2+e_3, e_2+e_3}, {e_0+e_1+e_2, e_1+e_2+e_3, e_2+e_4, e_0+e_1+e_2+e_4, e_0+e_1+e_2+e_4, e_0+e_1+e_2+e_4, e_0+e_2+e_3+e_4}, {0, 0, e_0+e_3+e_4, e_0+e_3+e_4, e_2+e_3, e_0+e_3+e_4, e_0+e_3+e_4}, {e_3+e_4, e_0, e_1+e_3, e_1+e_2+e_3, e_1+e_3+e_4, e_1+e_2, e_2+e_3}}
}
elapsedTime tally apply(2^10,c->(
	while(
	betti(a=sv*random(source sv,E^{7:-2}));
	betti (b=random(E^{-1},E^{7:-2}));
	rank source syz(a||b,DegreeLimit=>3) =!= 0) do ();
	B1=betti (F1=res(coker transpose (a||b),LengthLimit=>2,DegreeLimit=>1));
	B2=betti (F2=res(coker (a||b),LengthLimit=>2,DegreeLimit=>4));
	if rank F2_2 >16 then (<<"(B1,B2) = "<<(B1,B2)<<", c = " << c<<endl);
	if rank F2_2 >17 then  (mats=append(mats,(a||b));
	    <<toString (a||b) <<endl);
	(B1,B2)
	))
--break

log_2 65248
16-log_2 285 ,16-log_2 3
 659.192/60*2^3/60
#mats
tally apply(mats1,ab->(
B1=betti (T1=res(coker ab,LengthLimit=>5));
B2=betti (T2=res( coker transpose ab,LengthLimit=>5));
(B1,B2)))

-*
                    0 1  2  3  4   5   6         0 1  2  3  4   5   6
o49 = Tally{(total: 6 7 18 49 94 154 231, total: 7 6 11 35 82 160 279) => 4}
                 0: 6 7  .  .  .   .   .     -1: 7 6  1  .  .   .   .
                 1: . . 18 49 94 153 226      0: . .  3  7 11  15  19
                 2: . .  .  .  .   1   5      1: . .  7 28 71 145 260


*-

-* vectorbundle c1=0,c2=11  *-
restart
--needsPackage "NongeneralTypeSurfacesInP4"
kk=ZZ/3
E=kk[e_0..e_4,SkewCommutative=>true]
r0=2
m0 = matrix {{0, -e_0, 0, e_3+e_4, -e_2+e_4, -e_1, 0, 0, 0, -e_0+e_3, -e_2}, {e_0, 0, -e_0, 0, -e_2, 0, 0,
      0, -e_4, 0, e_0-e_2+e_4}, {0, e_0, 0, 0, 0, e_0, e_3, 0, 0, -e_3, -e_3+e_4}, {-e_3-e_4, 0, 0, 0, 0,
      -e_3, -e_0+e_3, 0, 0, 0, 0}, {e_2-e_4, e_2, 0, 0, 0, 0, 0, 0, 0, 0, 0}, {e_1, 0, -e_0, e_3, 0, 0,
      e_4, -e_2, e_3, 0, e_0-e_2}, {0, 0, -e_3, e_0-e_3, 0, -e_4, 0, 0, 0, 0, 0}, {0, 0, 0, 0, 0, e_2, 0,
      0, 0, e_0, 0}, {0, e_4, 0, 0, 0, -e_3, 0, 0, 0, 0, 0}, {e_0-e_3, 0, e_3, 0, 0, 0, 0, -e_0, 0, 0, 0},
      {e_2, -e_0+e_2-e_4, e_3-e_4, 0, 0, -e_0+e_2, 0, 0, 0, 0, 0}}
betti (fm0=res(coker m0,LengthLimit=>9,DegreeLimit=>4))
-*
              0  1  2  3   4   5   6   7   8    9   10   11   12
o15 = total: 11 11 22 60 127 237 403 641 969 1407 1977 2703 3611
          0: 11 11  .  .   .   .   .   .   .    .    .    .    .
          1:  .  . 20 47  82 129 188 260 346  447  564  698  850
          2:  .  .  2 13  45 108 215 381 623  960 1413 2005 2761
*-

n45=0;elapsedTime while (
      n20=0;elapsedTime while (
	   m1=matrix apply(11,i->apply(11,j->sum(5,k->(if random 100 <10 then random(kk) else 0_kk)*E_k)));
	      m=m1-transpose m1;
	betti (fm=res(coker m, LengthLimit=>2,DegreeLimit=>3));
	flatten degrees fm_2 =!= toList(20:3)) do (n20=n20+1);
    <<" m = " <<m<<endl;
    <<"n20 = "<<n20<<" "<<betti (fm=res(coker m,LengthLimit=>2,DegreeLimit=>4)); <<endl;
    r1=#flatten degrees fm_2-20;
    if r1<r0 then (r0=r1; m0=m);
    <<"r0 = "<<r0<<endl;
    rank fm_2 =!= 20 ) do n45=n45+1;


n20,n45 betti (fm=res(coker m, LengthLimit=>4,DegreeLimit=>5))
m0=m
betti fm
