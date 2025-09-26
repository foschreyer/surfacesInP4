chinH=method()
chinH(Number,Number,Number) := (m,d,sg) -> (binomial(m+1,2)*d-m*(sg-1)+1)
chiI=method()
chiI(Number,Number,Number) := (m,d,sg) -> binomial(m+4,4)-chinH(m,d,sg)


apply(toList(-1..7),n->chiI(n,12,13))

kk=ZZ/11
P4=kk[x_0..x_4]

prepareAboSurfaces=method()
prepareAboSurface(Ring) := P4 -> (
    kk=coefficientRing P4
    needsPackage("BGG")
    E=kk[e_0..e_4,SkewCommutative=>true]
    m2x3=matrix{{e_0,e_1,e_3},{e_1,e_2,e_4}}-- random(E^2,E^{3:-1})
    bs=flatten apply(4,i->flatten apply(2,j->apply(10,k->b_(i,j,k))))
    as=flatten apply(2,i->flatten apply(3,j->apply(10,k->a_(i,j,k))))
    B=kk[bs,as]
    ExB=E**B
    E2=sub(basis(2,E),ExB)
    b4x2=matrix apply(4,i->apply(2,j->sum(10,k->(b_(i,j,k)*E2_(0,k)))))
    a2x3=matrix apply(2,i->apply(3,j->sum(10,k->(a_(i,j,k)*E2_(0,k)))))
    E3=sub(basis(3,E),ExB)
)
