chinH=method()
chinH(Number,Number,Number) := (m,d,sg) -> (binomial(m+1,2)*d-m*(sg-1)+1)
chiI=method()
chiI(Number,Number,Number) := (m,d,sg) -> binomial(m+4,4)-chinH(m,d,sg)


apply(toList(-1..7),n->chiI(n,13,15))

b1=random(E^{3:0,2:1},E^{5:-1})
--b1=matrix apply(3,i->apply(5,j->E_(random(5))))
betti (sB1=syz b1)
betti(c=sB1*random(source sB1,E^{15:-3}))
betti(syz transpose c)
a1=random(E^2,E^{5:-1})
betti(sa1=syz a1)
betti(c=sa1*random(source sa1,E^{20:-3}))
betti syz transpose c 
kk=ZZ/3
P4=kk[x_0..x_4]


    kk=coefficientRing P4
    needsPackage("BGG")
    E=kk[e_0..e_4,SkewCommutative=>true]
    
    bs=flatten apply(5,i->flatten apply(2,j->apply(10,k->b_(i,j,k))))
    as=flatten apply(3,i->flatten apply(5,j->apply(10,k->a_(i,j,k))))
    B=kk[bs,as]
    numgens B
    ExB=E**B
    E2=sub(basis(2,E),ExB)
    b5x2=matrix apply(5,i->apply(2,j->sum(10,k->(b_(i,j,k)*E2_(0,k)))))
    a3x5=matrix apply(3,i->apply(5,j->sum(10,k->(a_(i,j,k)*E2_(0,k)))))
    E3=sub(basis(3,E),ExB)

    elapsedTime tally apply(3^3,i->(
	    m2x5=random(E^{2:-2},E^{5:-3});
	    m3x5=map(E^3,E^0,0);
	    scan(5,j->(while (m3x3=random(kk^3,kk^3); det m3x3==0) do ();
		   m3x5=m3x5|(m3x3*(m2x5_{j}||random(E^1,E^{1:-1})));
			   ));
	    m5x3=transpose m3x5;
	    c=b5x2*sub(m2x5,ExB)+sub(m5x3,ExB)*a3x5;
	    I=trim ideal sub(contract(E3,flatten c),B);
	    <<betti I<<endl;

	    sols=vars B%I;
	    betti(randSol=sub(sols,random(kk^1,kk^250)));
	    b5x2r=sub(b5x2,vars E|randSol);
	    betti(bb=map(E^5,,m5x3|b5x2r));
	    tally degrees source syz bb
	    ))
    betti syz bb
    betti res( coker transpose ((syz random(E^3,E^{3:-1,2:-2}))*random(E^{10:-3},E^{4:-3})),LengthLimit=>2)
    elapsedTime tally apply(3^2,c->
	betti res(coker random(E^{3:-1,2:-2},E^{5:-3}),LengthLimit=>2))

goodIs={}
elapsedTime tally apply(2^7,i->(
	while(
	    m2x5=random(E^{2:-2},E^{5:-3});
	    syz(m2x5,DegreeLimit=>3)==0) do();
  	m2x5=matrix apply(2,i->apply(5,j-> E_((i+j)%5)))
	    --m3x5=map(E^3,E^0,0);
	    --scan(5,j->(while (m3x3=random(kk^3,kk^3); det m3x3==0) do ();
	    --	   m3x5=m3x5|(m3x3*(m2x5_{j}||random(E^1,E^{1:-1})));
	--		   ));
	   while ( m5x3=random(E^5,E^{3:-1});
	       degrees source syz transpose m5x3=!={{2}, {2}, {2}, {2}, {2}, {2}, {2}, {2}, {2}, {2}, {2}, {2}, {2}, {2}, {2}, {2}, {2}, {2}, {2}, {2}}) do ();
           m5x3=matrix apply(5,i->apply(3,j->E_((i-j)%5)+E_((i-j-1)%5)))
	   c=b5x2*sub(m2x5,ExB)+sub(m5x3,ExB)*a3x5;
	    I=trim ideal sub(contract(E3,flatten c),B);
	    betti I
	    if numgens I <220 then goodIs=append(goodIs,I);
	    betti I))

tally apply(goodIs, I -> betti I)
I=last goodIs;
betti I
tally apply(goodIs,I->(
	sols=vars B%I;
	betti(randSol=sub(sols,random(kk^1,kk^250)));
	    b5x2r=sub(b5x2,vars E|randSol);
	    betti(bb=map(E^5,,m5x3|b5x2r));
	    (betti res(coker bb,LengthLimit=>2)),betti I
	))
    
