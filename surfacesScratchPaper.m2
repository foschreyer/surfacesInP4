
-- Quintic elliptic scroll (B2.1)
--     PURPOSE : Construct an quintic elliptic scroll, which is a nonsingular surface of degree 5 and sectional genus 1
--       INPUT : 'P4', the homogeneous coordinate ring of projective fourspace 
--      OUTPUT : Ideal of the quintic elliptic scroll
-- DESCRIPTION : This function constructs an quintic elliptic surface as the degeneracy locus of a map between two vector bundles

quinticEllipticScroll=method()
quinticEllipticScroll(PolynomialRing):=P4 -> (
    -- Compute the koszul complex of the variables of 'P4'
    kos:=res coker vars P4;
    -- Construct a variety 'X' as the degenerate locus of the map from 5O(-3) to the second Koszul syzygy module 
    X:=trim ideal syz transpose (kos.dd_4 | random(source kos.dd_3,P4^{5:-3}));
    -- Check whether 'X' is a surface with the desired degree and sectional genus 
    assert(dim X==3 and degree X==5 and sectionalGenus X==1);
    X)

-- Elliptic conic bundle which was missing in Okonek's paper
--     PURPOSE : Construct an elliptic conic bundle, which is a nonsingular surface of degree 8 and sectional genus 5
--       INPUT : 'P4', the homogeneous coordinate ring of projective fourspace 
--      OUTPUT : Ideal of the elliptic conic bundle
-- DESCRIPTION : This function constructs an quintic elliptic surface as the degeneracy locus of a map between two vector bundles

ellipticConicBundle=method()
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

-- Irregular elliptic surface of degree 12 and sectional genus 13 obtained as the dependency locus of two global sections of a rank three vector bundle
--     PURPOSE : Construct a nonsingular irregular elliptic surface of degree 12 and sectional genus 13
--       INPUT : 'P4', the homogeneous coordinate ring of projective fourspace 
--      OUTPUT : Ideal of the elliptic surface
-- DESCRIPTION : This function constructs an irregular elliptic surface as the degeneracy locus of a map between two vector bundles

irregularEllipticSurfaceD12=method()
irregularEllipticSurfaceD12(PolynomialRing) := P4 -> (
    -- Compute a koszul complex
    kos:=res coker matrix{{P4_0..P4_2,P4_3^2,P4_4^2}};
    -- Define a map from the second Koszul syzygy module to O(-1) 
    f:=map(P4^{1:-1},target kos.dd_3,{{1,4:0,-P4_0,2:0,P4_1,0}})*kos.dd_3;
     -- Construct the kernel of 'f'
    K:=prune homology(f,kos.dd_4);
    -- Define a variety 'X' as the degenerate locus of the map from O(-4)++3O(-5) to 'K'
    X:=trim ideal syz transpose (presentation K | random(source gens K,P4^{1:-4,3:-5}));
    -- Check whether 'X' is a surface with the desired degree and sectional genus 
    assert(dim X==3 and degree X==12 and sectionalGenus X==13);
    X)

-- Regular elliptic surface of degree 12 and sectional genus 13 obtained as the dependency locus of two global sections of an extension of the HM bundle (B7.7)
--     PURPOSE : Construct a nonsingular regular elliptic surface of degree 12 and sectional genus 13
--       INPUT : 'P4', the homogeneous coordinate ring of projective fourspace 
--      OUTPUT : Ideal of the elliptic surface
-- DESCRIPTION : This function constructs a regular elliptic surface as the dependency locus of two sections of a rank three vector bundle
--     COMMENT : This function uses the BGG package

regularEllipticSurfaceD12=method()
regularEllipticSurfaceD12(PolynomialRing) := P4 -> (
    KK:=coefficientRing P4;
    e symbol; 
    -- Define an exterior algebra
    E:=KK[e_0..e_4,SkewCommutative=>true];
    -- Define morphisms 'alpha' and 'beta' of modules over 'E'
    beta:=map(E^{5:0},E^{2:-2},{{e_4*e_1,e_2*e_3},{e_0*e_2,e_3*e_4},{e_1*e_3,e_4*e_0},{e_2*e_4,e_0*e_1},{e_3*e_0,e_1*e_2}});
    alpha:=syz beta;
    beta=random(E^{4:0},target beta)*beta;
    -- Construct a Beilison monad; we use the command 'beilinson' to return the associated maps between direct sums of exterior powers of cotangent bundles
    alpha=beilinson(alpha,R);
    beta=beilinson(beta,R);
    -- Compute the homology of the monad, which is a rank three vector bundle (this vector bundle is an extension of the HM bundle by a line bundle) 
    K:=prune homology(beta,alpha);
    -- Define a variety 'X' as the dependency locus of two global sections of 'K'
    X:=trim ideal syz transpose (presentation K | random(source gens K,R^{2:-2}));
    -- Check whether 'X' is a surface with the desired degree and sectional genus
    assert(dim X==3 and degree X==12 and sectionalGenus X==13);
    X)

-- Abelian surface of degree 10 obtained as the zero scheme of a global section of the HM bundle (B6.1)
--     PURPOSE : Construct a nonsingular abelian surface of degree 10 and sectional genus 6
--       INPUT : 'P4', the homogeneous coordinate ring of projective fourspace 
--      OUTPUT : Ideal of the abelian surface of degree 10
-- DESCRIPTION : This function the ideal of an abalian surface as the zero scheme of a global section of the Horrocks-Mumford bundle
--     COMMENT : This function uses the BGG package

abelianSurfaceD10=method()
abelianSurfaceD10(PolynomialRing):=P4 -> (
    KK:=coefficientRing P4;
    symbol e;
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
    assert(dim X==3 and degree X==10 and sectionalGenus X==6);
    X)

-- Abelian surface of degree 15, which is linkned to the HM abelian surface (B6.2)
--     PURPOSE : Construct a nonsingular abelian surface of degree 15 and sectional genus 21
--       INPUT : 'P4', the homogeneous coordinate ring of projective fourspace 
--      OUTPUT : Ideal of the abelian surface of degree 15
-- DESCRIPTION : This function constructs the abelian surface as the surface residual to the abelian surface of degree 10 in the (5,5) complete intersection
--     COMMENT : This function uses the BGG package and 'abelianSurfaceD10'

abelianSurfaceD15=method()
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

-- Abelian surface of degree 15 and sectional genus 21 (15.B1: Syz_2(N) is incorrect)
--     PURPOSE : Construct a nonsingular abelian surface of degree 15 and sectional genus 21
--       INPUT : 'P4', the homogeneous coordinate ring of projective fourspace 
--      OUTPUT : Ideal of the abelian surface of degree 15
-- DESCRIPTION : This function constructs the abelian surface as the dependency locus of two sections of a rank three vector bundle

abelianSurfaceD15S21Popescu=method()
abelianSurfaceD15S21Popescu(PolynomialRing):=P4->(
    -- Define three Moore matrices 'M1,' 'M2,' and 'M3'
    symbol z;
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
    X:=ideal syz transpose (ff.dd_4 |random(target ff.dd_4,P4^{15:-2,-3}));
    -- Check whether 'X' is a surface with the desired degree and sectional genus
    assert(dim X==3 and degree X==15 and sectionalGenus X==21);
    X)

-- K3 surface of degree 7 and sectional genus 5 (B4.3)
--     PURPOSE : Construct a nonsingular K3 surface of degree 7 and sectional genus 5
--       INPUT : 'P4', the homogeneous coordinate ring of projective fourspace 
--      OUTPUT : Ideal of the K3 surface of degree 7
-- DESCRIPTION : This function constructs the K3 surface as the degeneracy locus of a map between two vector bundles

K3surfaceD7=method()
K3surfaceD7(PolynomialRing):=P4 -> (
    -- Define a variety 'X' as the degeneracy locus of a generic map from O_PA(-1) ++ O_PA(-2) to 3O_PA 
    X:=minors(2,random(P4^{3:0},P4^{-1,-2}));
    -- Check whether 'X' is a surface with the desired degree and sectional genus
    assert(dim X==3 and degree X==7 and sectionalGenus X==5);
    X)

-- K3 surface of degree 8 and sectional genus 6 (B4.4)
--     PURPOSE : Construct a nonsingular K3 surface of degree 8 and sectional genus 6
--       INPUT : 'P4', the homogeneous coordinate ring of projective fourspace 
--      OUTPUT : Ideal of the K3 surface of degree 8
-- DESCRIPTION : This function constructs the K3 surface as the degeneracy locus of a map between two vector bundles

K3surfaceD8=method()
K3surfaceD8(PolynomialRing) := P4 -> (
    -- Compute the koszul complex of the variables of 'P4'
    kos:=res coker vars P4;
    -- Construct 'X' as the degeneracy locus of a generic map from O_P4(-3) ++ 2O_P4(-2) to the cotangent bundle 
    X:=ideal syz transpose (kos.dd_3 | random(target kos.dd_3,P4^{2:-2,-3}));
    -- Check whether 'X' is a surface with the desired degree and sectional genus
    assert(dim X==3 and degree X==8 and sectionalGenus X==6);
    X)

-- K3 surface of degree 9 and sectional genus 8 (B4.5)
--     PURPOSE : Construct a nonsingular K3 surface of degree 9 and sectional genus 8
--       INPUT : 'P4', the homogeneous coordinate ring of projective fourspace 
--      OUTPUT : Ideal of the K3 surface of degree 9
-- DESCRIPTION : This function constructs the K3 surface as the degeneracy locus of a map between two vector bundles

K3surfaceD9=method()
K3surfaceD9(PolynomialRing) := P4 -> (
    -- Compute the koszul complex of the variables of 'P4'
    kos:=res coker vars P4;
    -- Define the direct sum 'f' of the fourth exterior power of the cotangent bundle and O_PA(_4)
    f:=kos.dd_4 ++ map(P4^{-4},P4^{-4},1);
    -- Define 'X' as the degeneracy locus of a general map from 'f' to 6O_P4(-3)
    X:=ideal syz transpose (random(P4^{6:-3},target f)*f);
    -- Check whether 'X' is a surface with the desired degree and sectional genus
    assert(dim X==3 and degree X==9 and sectionalGenus X==8);
    X)

-- K3 surface of degree 10 and sectional genus 9 with one 6-secant line (this script is a little cheating) (B4.6)
--     PURPOSE : Construct a nonsingular K3 surface of degree 10 and sectional genus 9 with one 6-secant line
--       INPUT : 'P4', the homogeneous coordinate ring of projective fourspace 
--      OUTPUT : Ideal of the K3 surface of degree 10 with one 6-secant line
-- DESCRIPTION : This function constructs the ideal of the K3 surface as the homology of a Beilinson monad
--     COMMENT : This function uses the BGG package

K3surfaceD10S9SL1=method()
K3surfaceD10S9SL1(PolynomialRing) := P4 -> (
    KK:=coefficientRing P4;
    symbol e;
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
    X:=trim ideal syz transpose presentation I;
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

-- K3 surface of degree 11 and sectional genus 11 witha 6-secant lines (B4.8-11)
--     PURPOSE : Construct a nonsingular K3 surface of degree 11 and sectional genus 11 with a 6-secant lines
--       INPUT : 'P4', the homogeneous coordinate ring of projective fourspace and an integer between 0 and 3 
--      OUTPUT : Ideal of the K3 surface of degree 10 with one 6-secant line
-- DESCRIPTION : This function constructs the ideal of the K3 surface as the degeneracy locus of a map between two vector bundles
--     COMMENT : This function uses 'H1module,' a command that takes "P4' and an integer between 0 and 3 and returns the H1 module of the ideal sheaf of the surface 

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

K3SurfaceD11G11SLa=method()
K3SurfaceD11G11SLa(PolynomialRing,ZZ):=(P4,a)->(
    var:=vars P4;
    -- Calculate the direct sum of two Koszul complexes
    kos:=res coker (var++var);
    -- Denote by 'Omega' the third syzygy module sheaf of 'var++var'
    omega:=map(P4^{10:-1},,kos.dd_5);
    -- Use 'H1module' to construct the sheafified first syzygy module a module of finite length 
    f:=H1module(P4,a);
    ff:=res coker f;
    -- Choose randomly a map 'p' from the direct sum of O_P4(-1) and the two copies of the third exterior power of the cotangent bundle twisted by 3 to the first syzygy module sheaf of 'coker f'
    p1:=transpose ((random(target transpose omega,target transpose ff.dd_1)*transpose ff.dd_1) // transpose omega);
    p2:=random(target p1,P4^{1:-1});
    p:=ff.dd_1 | (p2 | p1);
    -- Construct 'X' as the degeneracy locus of 'p'
    X:=trim ideal syz transpose p;
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
    symbol e;
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
    symbol e;
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
    symbol e;
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
    symbol e;
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
    symbol e;
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
    symbol e;
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
    symbol e;
    -- Define an exterior algebra
    E:=KK[e_0..e_4,SkewCommutative => true];
    -- Choose morphisms 'f' and 'g' over 'E' randomly 
    f:=random(E^{1:0},E^{1:-1,2:-2});
    g:=(syz f)*random(source syz f,E^{3:-3,2:-4});
    -- Construct a Beilison monad; we use the command 'beilinson' to return the associated maps between direct sums of exterior powers of twisted cotangent bundles
    I:=prune homology(beilinson(f,P4),beilinson(g,P4));
    -- Construct 'X' as the scheme of 'I'
    X:=trim ideal syz transpose presentation I;
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
    symbol e;
    -- Define an exterior algebra
    E:=KK[e_0..e_4,SkewCommutative => true];
    -- Choose a specific morphism 'f' over 'E' 
    f:=map(E^{1:0},E^{1:-1,2:-2},{{e_2,e_0*e_1,0}});
    -- Choose a morphism 'g' over E randomly
    g:=(syz f)*random(source syz f,E^{3:-3,2:-4});
    -- Construct a Beilison monad; we use the command 'beilinson' to return the associated maps between direct sums of exterior powers of twisted cotangent bundles
    I:=prune homology(beilinson(f,P4),beilinson(g,P4));
    -- Construct 'X' as the scheme of 'I'
    X:=trim ideal syz transpose presentation I;
    -- Check whether 'X' is a surface with the desired degree and sectional genus
    assert(dim X==3 and degree X==12 and sectionalGenus X==14);
    X)

