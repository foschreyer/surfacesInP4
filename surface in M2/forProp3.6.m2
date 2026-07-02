restart
needsPackage "NongeneralTypeSurfacesInP4"
setRandomSeed("twice  splitting")
kk=ZZ/nextPrime 10^2
P5=kk[b_0..b_5]
N=random(P5^5,P5^{5:-1})
J=pfaffians(4,N-transpose N)
(degree J, sectionalGenus J)==(5,1)

parametrizationOfDegreeFiveDelPezzo=method()
parametrizationOfDegreeFiveDelPezzo(Ideal) := J -> (
    P5 := ring J;
    kk := coefficientRing P5;
    fJ := res J;
    ta := betti fJ;
    tb := new BettiTally from {(0,{0},0) => 1, (1,{2},2) => 5, (2,{3},3) => 5, (3,{5},5) => 1};
    if ta != tb then error "expected a DelPezzo surface of degree 5";
    if not saturate ideal singularLocus(P5/J) == ideal 1_P5 then "expected a smooth surface";
    m10x5 := syz(fJ.dd_1|map(P5^1,,transpose fJ.dd_3),DegreeLimit=>2);
    aut := sub(m10x5^{0..4},kk);
    M := (inverse aut)*fJ.dd_2;
    assert(M+transpose M==0);
    -- We compute the projective dual, which consist of five points.
    -- These correspond to the 5 pencil of conics on V(J) \subset P5
    g:=symbol g;
    P9 := kk[g_0..g_9];
    N := genericSkewMatrix(P9,g_0,5);
    --flatten apply(5,i->apply(toList(i+1..4),j->N_(i,j)))
    subst := matrix{flatten apply(5,i->apply(toList(i+1..4),j->M_(i,j)))};
    betti(m10x4 := syz(subst,DegreeLimit =>1));
    w:=symbol w;
    P3 := kk[w_0..w_3];
    betti(subst2 := vars P3*transpose sub(m10x4,kk));
    betti(M' := sub(N,subst2));
    fivePoints := pfaffians(4,M');
    c5Pts := decompose fivePoints;    
    netList apply(c5Pts,c->(dim c, degree c))
    perhapsTwoPoints := select(c5Pts,c->degree c==1)
    if #perhapsTwoPoints>1 then (twoPoints:=perhapsTwoPoints_{0,1}; kk':= kk;
	   d1:=1;P3':=kk[gens P3];
	   twoPoints=sub(twoPoints,P3')) else (
	notkkRationalPoints=select(c5Pts,c->degree c>1);
	d1=min apply(notkkRationalPoints,c->degree c);
	d1Pts:=(select(notkkRationalPoints,c->degree c==d1))_0;
	kk1 = GF(char kk,d1);
	P3' = kk1[gens P3];
	twoPoints=(decompose sub(d1Pts,P3'))_{0,1});
    P5':= kk1[gens P5];
    J':=sub(J,P5');
    twoPoints=apply(twoPoints,p->
       sub(transpose syz transpose jacobian p,kk1));
    A:=null;B:=null;
    ABs:=apply(twoPoints,p->(
	    M'p=sub(sub(M',P3'),p);
	    A=syz(M'p);B=syz(transpose A);(A,B)));
    pencilsMats:=apply(ABs,(A,B) -> transpose A*sub(M,P5')*B);
    pencils:=apply(pencilsMats, m3x2-> minors(2,m3x2));
    assert(all apply(pencils,I->I+J'==J'));
    assert(J'==sum pencils);
    -- parametization from P1xP1
    y=symbol y; z=symbol z;
    P1xP1:=kk1[y_0,y_1,z_0,z_1,Degrees=>{2:{1,0},2:{0,1}}]
    P1xP1xP5:=P1xP1**P5'    
    yPencil:=sub(basis({1,0},P1xP1),P1xP1xP5)*sub(transpose pencilsMats_0,P1xP1xP5);
    zPencil:=sub(basis({0,1},P1xP1),P1xP1xP5)*sub(transpose pencilsMats_1,P1xP1xP5);
    betti(m6x6:=contract(transpose sub(vars P5',P1xP1xP5),yPencil|zPencil));
    betti (paraJ:=map(P1xP1^1,,transpose sub(syz transpose m6x6,P1xP1)));
    phi:=map(P1xP1,P5',paraJ);
    assert(ker phi == J');
    basePts=saturate(saturate(minors(5,sub(m6x6,P1xP1)),ideal basis({1,0},P1xP1)),ideal basis({0,1},P1xP1))    
    cBasePts=decompose basePts;
    tally apply(cBasePts,c->(dim c, degree c));
    d2:= min apply(cBasePts, c->degree c);    
    kk2:=GF(char kk,d1*d2,Variable=>e);
    P5'=kk2[gens P5];
    J'=sub(J,P5');
    P3'=kk2[gens P3];
    betti(M' = sub(M',P3'));
    fivePoints = pfaffians(4,M');
    c5Pts = decompose fivePoints;    
    perhapsTwoPoints = select(c5Pts,c->degree c==1);
    twoPoints=perhapsTwoPoints_{0,1}; 
    twoPoints=apply(twoPoints,p->
       sub(transpose syz transpose jacobian p,kk2));
    ABs=apply(twoPoints,p->(
	    M'p=sub(sub(M',P3'),p);
	    A=syz(M'p);B=syz(transpose A);(A,B)));
    pencilsMats=apply(ABs,(A,B) -> transpose A*sub(M,P5')*B);
    pencils=apply(pencilsMats, m3x2-> minors(2,m3x2));
    assert(all apply(pencils,I->I+J'==J'));
    assert(J'==sum pencils);
    -- parametization from P1xP1
    y=symbol y; z=symbol z;
    P1xP1=kk2[y_0,y_1,z_0,z_1,Degrees=>{2:{1,0},2:{0,1}}];
    P1xP1xP5=P1xP1**P5'    
    yPencil:=sub(basis({1,0},P1xP1),P1xP1xP5)*sub(transpose pencilsMats_0,P1xP1xP5);
    zPencil:=sub(basis({0,1},P1xP1),P1xP1xP5)*sub(transpose pencilsMats_1,P1xP1xP5);
    betti(m6x6=contract(transpose sub(vars P5',P1xP1xP5),yPencil|zPencil));
    betti (paraJ=map(P1xP1^1,,transpose sub(syz transpose m6x6,P1xP1)));
    phi=map(P1xP1,P5',paraJ);    
    basePts=saturate(saturate(minors(5,sub(m6x6,P1xP1)),
	    ideal basis({1,0},P1xP1)),ideal basis({0,1},P1xP1));    
    cBasePts=decompose basePts;
    pOnP1xP1=first cBasePts;
    assert(degree pOnP1xP1 ==1);
    c1=sub(contract(z_1,pOnP1xP1_0),kk2),c2=sub(contract(y_1,pOnP1xP1_1),kk2);
    u=symbol u;
    P2'=kk2[u_0..u_2];
    paraP2=matrix{{u_0-u_1*c2,u_1,u_0-c1*u_2,u_2}};
    sub(pOnP1xP1,sub(paraP2,matrix{{0,2,1_kk2}}))
    paraJ2=contract(u_0,sub(paraJ,paraP2));
    trim ker map(P2',P5',paraJ2)==sub(J,P5');
    baseLocus=saturate ideal paraJ2;
    assert(#decompose baseLocus == 4);
    paraJ2)

    betti(paraX=map(P2'^1,,transpose syz transpose sub(L1_0,paraJ2)))
    betti(baseLocus=saturate ideal paraX)
    rBaseLocus=radical baseLocus
    quartic=ideal rBaseLocus_0
    fourPoints=baseLocus:rBaseLocus;degree fourPoints
    twelvePoints=rBaseLocus:fourPoints; degree twelvePoints
    betti intersect (apply(decompose fourPoints,p->saturate(p^2+quartic))|{twelvePoints}) 
