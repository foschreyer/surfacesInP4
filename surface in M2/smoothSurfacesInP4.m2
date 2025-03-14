
chiITable=method()
chiITable(Number,Number) := (d,sg) -> apply(toList(-1..5),m->chiI(m,d,sg))

castelnouvoSurface=method()
castelnouvoSurface(Ring) := P4 -> minors(2,random(P4^{-2,2:-3},P4^{2:-4}))

bordigaSurface=method()
bordigaSurface(Ring) := P4 -> minors(3,random(P4^{4:-3},P4^{3:-4}))

veroneseSurface=method()
veroneseSurface(Ring,Ring) := (P4,P2) -> (
    kk := coefficientRing P2;
    h:=basis(2,P2)*syz random(kk^1,kk^6); 
    X:=trim ker map(P2,P4,h);
    assert(degree X ==4 and dim X==3);
    X)
TEST ///
chiITable(4,1)
///
end
load"smoothSurfacesInP4"
kk=ZZ/nextPrime 10^3
P4=kk[x_0..x_4]
P2=kk[t_0..t_2]


    
TEST ///
minimalBetti(X=castelnouvoSurface(P4)),degree X
genX=genera X
chiITable(degree X,genX_1)

minimalBetti(X=bordigaSurface(P4)),degree X
genX=genera X
chiITable(degree X,genX_1)

minimalBetti(X=veroneseSurface(P4,P2)),degree X
genX=genera X
chiITable(degree X,genX_1)

///

minimalBetti(X=minors(2,random(P4^3,P4^{-1,-2})))
degree Xgenera X
