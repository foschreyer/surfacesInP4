    i1 : kk=ZZ/nextPrime 10^3;
    i2 : P4=kk[x_0..x_4];
    i3 : E=kk[e_0..e_4,SkewCommutative=>true];
    setRandomSeed("fix decomposition")
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

    -- Text
    
    elapsedTime (L0,L1,L2,J)=adjunctionProcess(X,3);
    L0
    P5=ring J
    fJ=res J
    m10x5=syz(fJ.dd_1|map(P5^1,,transpose fJ.dd_3),DegreeLimit=>2)
    aut=sub(m10x5^{0..4},kk)
    fJ.dd_1*aut==-map(P5^1,,transpose fJ.dd_3)
    M=(inverse aut)*fJ.dd_2
    M+transpose M==0
    --Text compute the projective dual, which consist of five points.
    -- These correspond to the 5 pencil of conics on V(J) \subset P5 
    P9=kk[b_0..b_9]
    N=genericSkewMatrix(P9,b_0,5)
    flatten apply(5,i->apply(toList(i+1..4),j->N_(i,j)))
    subst=matrix{flatten apply(5,i->apply(toList(i+1..4),j->M_(i,j)))};
    betti(m10x4=syz(subst,DegreeLimit =>1))
    P3=kk[c_0..c_3]
    betti(subst2=vars P3*transpose sub(m10x4,kk))
    betti(M'=sub(N,subst2))
    fivePoints=pfaffians(4,M');
    c5Pts=decompose fivePoints    
    netList apply(c5Pts,c->(dim c, degree c))
    twoPoints=apply(c5Pts_{0,1},c->sub(transpose syz transpose jacobian c,kk))
    ABs=apply(twoPoints,p->(M'p=sub(M',p); A=syz(M'p);
	    B=syz(transpose A);(A,B)))
    pencilsMats=apply(ABs,(A,B) -> transpose A*M*B)
-*
P2=kk[z_0..z_2]    
m3x2=first pencilsMats
P5=ring m3x2    
P2xP5=P2**P5
betti (g2=minors(2,(sub(vars P2,P2xP5)||transpose sub(m3x2,P2xP5)))+sub(J,P2xP5))
betti (g2s=saturate(g2,sub(ideal vars P5,P2xP5)))
degrees source gens g2s
betti(g2ss=saturate(g2s,sub(ideal vars P2,P2xP5)))
betti(graph=ideal(sub(vars P2,P2xP5)*sub(m3x2,P2xP5))+sub(J,P2xP5))
degrees source gens graph
betti (graph1=saturate(graph,sub(ideal vars P5,P2xP5)))
sg=syz gens graph
sg^{0,1}
positiondegrees source sg
*-
    pencils=apply(pencilsMats, m3x2-> minors(2,m3x2));
    all apply(pencils,I->I+J==J)
    J==sum pencils
    -- parametization from P1xP1
    P1xP1=kk[y_0..z_1,Degrees=>{2:{1,0},2:{0,1}}]
    P1xP1xP5=P1xP1**P5    
    yPencil=sub(basis({1,0},P1xP1),P1xP1xP5)*sub(transpose pencilsMats_0,P1xP1xP5);
    zPencil=sub(basis({0,1},P1xP1),P1xP1xP5)*sub(transpose pencilsMats_1,P1xP1xP5);
    betti(m6x6=contract(transpose sub(vars P5,P1xP1xP5),yPencil|zPencil))
    betti (paraJ=map(P1xP1^1,,transpose sub(syz transpose m6x6,P1xP1)))
    phi=map(P1xP1,P5,paraJ)
    P3=kk[w_0..w_3]
    segre1=basis({1,0},P1xP1)**basis({0,1},P1xP1)
    segre=map(P1xP1,P3,segre1)
    Q=ker segre
    P1xP1xP3=P1xP1**P3
    g=ideal apply(4,i->sub(segre1_(0,i),P1xP1xP3)-sub(w_i,P1xP1xP3))
    paraQ=sub(sub(paraJ,P1xP1xP3)%g,P3)
    phiQ=map(P3/Q,P5,paraQ)
    degrees source paraJ
    ker phi==J
    ker phiQ==J
    basePts=saturate(saturate(minors(5,sub(m6x6,P1xP1)),ideal basis({1,0},P1xP1)),ideal basis({0,1},P1xP1))    
    cBasePts=decompose basePts
    tally apply(cBasePts,c->(dim c, degree c))
    kk3=GF(char kk,3)
    P1xP1'=kk3[gens P1xP1,Degrees=>degrees P1xP1]
    cBasePts=decompose sub(basePts,P1xP1');
    tally apply(cBasePts,c->(dim c, degree c))
    pOnP1xP1=first cBasePts
    c1=sub(contract(z_1,pOnP1xP1_0),kk3),c2=sub(contract(y_1,pOnP1xP1_1),kk3)
    P2'=kk3[u_0..u_2]
    gens P1xP1'
    segre
    paraP1xP1=matrix{{c2*u_0,-u_1}}**matrix{{c1*u_0,-u_2}}
    paraJ1=sub(paraJ,paraP1xP1)
    paraJ2=contract(u_1^2*u_0^2,paraJ1)
    primaryDecomposition ideal paraJ2
    primaryDecomposition ideal paraJ
    paraJ1
    betti (paraJ2=map(P2'^1,,paraJ1))
    paraJ2
    P5'=kk3[gens P5]
    ker map(P2',P5',paraJ1)==sub(J,P5')
    baseLocus=decompose ideal paraJ2
