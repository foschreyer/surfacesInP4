-- Quintic elliptic scroll

quinticEllipticScroll=method()
quinticEllipticScroll(PolynomialRing) := P4 -> (
    kos:=res coker vars P4;
    X:=trim ideal syz transpose (kos.dd_4 | random(source kos.dd_3,R^{5:-3}));
    assert(dim X==3 and degree X==5 and sectionalGenus X==1);
    X)

-- Elliptic conic bundle which was missing in Okenek's paper

ellipticConicBundle=method()
ellipticConicBundle(PolynomialRing) := P4 -> (
    kos:=res coker matrix{{P4_0..P4_2,P4_3,P4_4^2}};
    f:=map(P4^{1:-1},target kos.dd_3,{{1,3:0,2:1,4:0}})*kos.dd_3;
    K:=prune homology(f,kos.dd_4);
    X:=trim ideal syz transpose (presentation K | random(source gens K,P4^{4:-4}));
    assert(dim X==3 and degree X==8 and sectionalGenus X==5);
    X)

-- Irregular elliptic surface of degree 12 and sectional genus 13 obtained as the dependency locus of two global sections of a rank three vector bundle

irregularEllipticSurfaceD12=method()
irregularEllipticSurfaceD12(PolynomialRing) := P4 -> (
    kos:=res coker matrix{{P4_0..P4_2,P4_3^2,P4_4^2}};
    f:=map(P4^{1:-1},target kos.dd_3,{{1,4:0,-P4_0,2:0,P4_1,0}})*kos.dd_3;
    K:=prune homology(f,kos.dd_4);
    X:=trim ideal syz transpose (presentation K | random(source gens K,P4^{1:-4,3:-5}));
    assert(dim X==3 and degree X==12 and sectionalGenus X==13);
    X)

-- Regular elliptic surface of degree 12 and sectional genus 13 obtained as the dependency locus of two global sections of an extension of the HM bundle

regularEllipticSurfaceD12=method()
regularEllipticSurfaceD12(PolynomialRing) := P4 -> (
    KK:=coefficientRing P4;
    E:=KK[e_0..e_4,SkewCommutative=>true];
    beta:=map(E^{5:0},E^{2:-2},{{e_4*e_1,e_2*e_3},{e_0*e_2,e_3*e_4},{e_1*e_3,e_4*e_0},{e_2*e_4,e_0*e_1},{e_3*e_0,e_1*e_2}});
    alpha:=syz beta;
    beta=random(E^{4:0},target beta)*beta;
    alpha=beilinson(alpha,R);
    beta=beilinson(beta,R);
    K:=prune homology(beta,alpha);
    X:=trim ideal syz transpose (presentation K | random(source gens K,R^{2:-2}));
    assert(dim X==3 and degree X==12 and sectionalGenus X==13);
    X)

-- Abelian surface of degree 10 obtained as the zero scheme of a global section of the HM bundle

abelianSurfaceD10=method()
abelianSurfaceD10(PolynomialRing) := P4 -> (
    KK:=coefficientRing P4;
    symbol e;
    E:=KK[e_0..e_4,SkewCommutative=>true];
    alphad:=map(E^{5:0},E^{2:-2},{{e_4*e_1,e_2*e_3},{e_0*e_2,e_3*e_4},{e_1*e_3,e_4*e_0},{e_2*e_4,e_0*e_1},{e_3*e_0,e_1*e_2}});
    alpha:=syz alphad;
    alphad=beilinson(alphad,P4);
    alpha=beilinson(alpha,P4);
    K:=prune homology(alphad,alpha);
    X:=trim ideal syz transpose (presentation K | random(source gens K,P4^{1:-3}));
    assert(dim X==3 and degree X==10 and sectionalGenus X==6);
    X)

-- Abelian surface of degree 15, which is linkned to the HM abelian surface

abelianSurfaceD15=method()
abelianSurfaceD15(PolynomialRing) := P4 -> (
    Y:=abelianSurfaceD10(P4);
    V:=ideal (gens Y*random(source gens Y,P4^{2:-5}));
    X:=V:Y;
    assert(dim X==3 and degree X==15 and sectionalGenus X==21);
    X)

-- K3 surface of degree 7 and sectional genus 5

K3surfaceD7=method()
K3surfaceD7(PolynomialRing) := P4 -> (
    X:=minors(2,random(P4^{3:0},P4^{-1,-2}));
    assert(dim X==3 and degree X==7 and sectionalGenus X==5);
    X)

-- K3 surface of degree 8 and sectional genus 6

K3surfaceD8=method()
K3surfaceD8(PolynomialRing) := P4 -> (
    kos:=res coker vars P4;
    X:=ideal syz transpose (kos.dd_3 | random(target kos.dd_3,P4^{2:-2,-3}));
    assert(dim X==3 and degree X==8 and sectionalGenus X==6);
    X)

-- K3 surface of degree 9 and sectional genus 8

K3surfaceD9=method()
K3surfaceD9(PolynomialRing) := P4 -> (
    kos:=res coker vars P4;
    f:=kos.dd_4 ++ map(P4^{-4},P4^{-4},1);
    X:=ideal syz transpose (random(P4^{6:-3},target f)*f);
    assert(dim X==3 and degree X==9 and sectionalGenus X==8);
    X)
    
-- Elliptic surface of degree 7 and sectional genus 6

ellipticSurfaceD7=method()
ellipticSurfaceD7(PolynomialRing) := P4 -> (
    X:=minors(2,random(P4^{1:1,2:-1},P4^{2:-2}));
    assert(dim X==3 and degree X==7 and sectionalGenus X==6);
    X)

-- Elliptic surface of degree 8 and sectional genus 7

ellipticSurfaceD8=method()
ellipticSurfaceD8(PolynomialRing) := P4 -> (
    X:=minors(2,random(P4^{2:1,1:0},P4^{2:-1}));
    assert(dim X==3 and degree X==8 and sectionalGenus X==7);
    X)

-- Elliptic surface of degree 9 and sectional genus 7

ellipticSurfaceD9=method()
ellipticSurfaceD9(PolynomialRing) := P4 -> (
    KK:=coefficientRing P4;
    kos:=res coker vars P4;
    f:=map(P4^{2:-1},P4^{2:-1},1)++map(P4^{15:-1},,kos.dd_2++kos.dd_2++kos.dd_2);
    symbol e;
    E:=KK[e_0..e_4,SkewCommutative=>true];
    syzf:=syz f;
    g:=map(target syzf,,beilinson(random(E^{2:0,3:-1},E^{2:-2,-4}),P4));
    X:=prune ideal syz transpose (syzf | g);
    assert(dim X==3 and degree X==9 and sectionalGenus X==7);
    X)

-- Elliptic surface of degree 10 and sectional genus 9

ellipticSurfaceD10S9=method()
ellipticSurfaceD10S9(PolynomialRing) := P4 -> (
    KK:=coefficientRing P4;
    E:=KK[e_0..e_4,SkewCommutative => true];
    f:=random(E^{1:0},E^{3:-1}) | map(E^{1:0},E^{1:0},0);
    g:=(syz f)*random(source syz f,E^{-2,-3,-4});
    beta:=beilinson(f,P4);
    alpha:=beilinson(g,P4);
    I:=prune homology(beta,alpha);
    X:=prune ideal syz transpose presentation I;
    assert(dim X==3 and degree X==10 and sectionalGenus X==9);
    X)
    

-- Elliptic surface of degree 10 and sectional genus 10

ellipticSurfaceD10S10=method()
ellipticSurfaceD10S10(PolynomialRing) := P4 -> (
    KK:=coefficientRing P4;
    kos:=res coker vars P4;
    f:=map(P4^{3:-1},P4^{3:-1},1)++map(P4^{5:-1},,kos.dd_2);
    syzf:=syz f;
    symbol e;
    E:=KK[e_0..e_4,SkewCommutative=>true];
    g:=map(target syzf,,beilinson(random(E^{3:0,1:-1},E^{1:-3,2:-4}),P4));
    X:=prune ideal syz transpose (syzf | g);
    assert(dim X==3 and degree X==10 and sectionalGenus X==10);
    X)

-- Elliptic surface of degree 11 and sectional genus 12

ellipticSurfaceD11=method()
ellipticSurfaceD11(PolynomialRing) := P4 -> (
    KK:=coefficientRing P4;
    kos:=res coker vars P4;
    f:=map(P4^{-1},P4^{-1},1)++map(P4^{15:-1},,kos.dd_2++kos.dd_3);
    syzf:=syz f;
    symbol e;
    E:=KK[e_0..e_4,SkewCommutative=>true];
    g:=map(target syzf,,beilinson(random(E^{0,-1,-2},E^{2:-3,2:-4}),P4));
    X:=prune ideal syz transpose (syzf | g);
    assert(dim X==3 and degree X==11 and sectionalGenus X==12);
    X)

-- Elliptic surface of degree 12 and sectional genus 14

ellipticSurfaceD12S14=method()
ellipticSurfaceD12S14(PolynomialRing) := P4 -> (
    KK:=coefficientRing P4;
    E:=KK[e_0..e_4,SkewCommutative => true];
    f:=random(E^{1:0},E^{1:-1,2:-2});
    g:=(syz f)*random(source syz f,E^{3:-3,2:-4});
    I:=prune homology(beilinson(f,P4),beilinson(g,P4));
    X:=prune ideal syz transpose presentation I;
    assert(dim X==3 and degree X==12 and sectionalGenus X==14);
    X)


