restart
-- surface of degree 11, sectional genus pi=10 and pg=q=0
p=3
kk=ZZ/p
P4=kk[x_0..x_4]
betti (F=res(ideal vars P4, LengthLimit=>3))
3.19/1000*p^6/60 --minutes

betM:=()->(while (
	M:=ideal (F.dd_3*random(F_3,P4^{-4}));
	apply(4,i->hilbertFunction(i,M))!={1,5,5,0}) do ();
    bet:=minimalBetti(M,LengthLimit=>3))
betM()
elapsedTime tal=tally apply(p^7,c->betM())

v=(values tal)_1
log(p,p^6/v)

findSurface=method()
findSurface(Ring) := P4 -> (
    F:=res(ideal vars P4, LengthLimit=>3);
    kk:=coefficientRing P4;
    M:=nil;fM:=nil;N:=nil;N1:=nil;
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
    J1:=syz transpose (fM.dd_2*syz transpose syz(transpose(fM.dd_3*N1),DegreeLimit=>-3));
    source J1 != P4^{0,-2}) do ();
    trim ideal(transpose J1_{1}*syz(fM.dd_1))
    )

elapsedTime J=findSurface P4;betti J
minimalBetti J
elapsedTime tally apply(10,i-> (J=findSurface P4;
	(genera J, minimalBetti J)))


betti(singX=saturate(J+minors(2,jacobian J)))
dim singX
findSmoothSurface=method(Options=>{Verbose=>true})
findSmoothSurface(Ring) := opt -> (P4 -> (
	if opt.Verbose==true then (
    while (
     elapsedTime while (J=findSurface P4; dim (J+ideal jacobian J)!=0) do ();
	elapsedTime singX:=J+minors(2,jacobian J);<<endl;
	elapsedTime dim singX !=0) do ();) else (
    while (
	while (J=findSurface P4; dim (J+ideal jacobian J)!=0) do ();
	 singX:=J+minors(2,jacobian J);
	 dim singX !=0) do ());
   J))
///
setRandomSeed("surface2") -- p=3 -- 14.6751 seconds elapsed
elapsedTime betti (X=findSmoothSurface P4)
minimalBetti X
setRandomSeed("surface3")
elapsedTime betti (X=findSmoothSurface(P4,Verbose=>false))
///

surfaceFromModule=method()
surfaceFromModule(Ideal) := M -> (
    fM=res(M);
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

 

moduleFromSurface=method()
moduleFromSurface(Ideal) := X -> (
    betti(fX:=res X);
    betti (fN:=res(coker transpose fX.dd_4));
    ideal fN.dd_5)


TEST ///
M=moduleFromSurface X
minimalBetti M
X'=surfaceFromModule M;
X==X'
///
smoothSurfaces={}

elapsedTime tally apply(3^3,i->(elapsedTime X=findSmoothSurface(P4,Verbose=>false);
	smoothSurfaces=append(smoothSurfaces,X);betti X))

2638.3/27/60

tally apply(smoothSurfaces,X->betti X)	
tally apply(smoothSurfaces,X->(X5= ideal (gens X)_{0..4};
	R=X5:X;
	(degree R, dim R, betti X, degree (X+R))))

surfacesWithSpecial6secants=select(smoothSurfaces,X->(X5= ideal (gens X)_{0..4};
	R=X5:X; dim R==3));
Mspecial=apply(surfacesWithSpecial6secants,X->moduleFromSurface(X));
toString Mspecial

Mspecial1={ideal(x_0*x_1+x_1^2+x_0*x_2+x_1*x_2+x_0*x_3-x_1*x_3+x_2*x_3+x_3^2-x_0*x_4+x_2*x_4+x_3
      *x_4+x_4^2,x_1*x_3+x_3^2-x_0*x_4-x_1*x_4-x_2*x_4+x_3*x_4,x_2^2+x_1*x_3+x_3*x_4+x_4^2,x
      _0*x_2-x_0*x_3-x_1*x_3-x_3^2+x_0*x_4-x_1*x_4-x_2*x_4-x_3*x_4-x_4^2,x_0*x_3+x_1*x_3-x_3
      ^2-x_1*x_4-x_4^2,-x_1*x_2+x_0*x_3+x_1*x_3+x_2*x_3+x_3^2+x_0*x_4+x_1*x_4+x_2*x_4+x_4^2
      ,-x_0*x_1+x_0*x_3+x_3^2-x_2*x_4+x_3*x_4+x_4^2,x_0*x_3-x_1*x_3+x_3^2-x_0*x_4+x_1*x_4-x_
      2*x_4-x_3*x_4,x_0*x_2-x_1*x_3+x_3^2+x_0*x_4+x_1*x_4+x_3*x_4-x_4^2,x_0^2-x_2*x_3-x_3^2+
      x_0*x_4+x_4^2), ideal(-x_2*x_3-x_3^2-x_1*x_4+x_2*x_4+x_3*x_4,x_1*x_2-x_2*x_4-x_4^2,x_0
      *x_2+x_1*x_2-x_2^2-x_2*x_3+x_3^2-x_0*x_4+x_1*x_4+x_2*x_4+x_3*x_4,x_2^2+x_0*x_3+x_1*x_3
      -x_2*x_3+x_3^2-x_0*x_4+x_1*x_4-x_3*x_4,-x_1^2-x_0*x_3+x_2*x_3-x_0*x_4+x_2*x_4+x_3*x_4
      ,-x_0*x_1-x_1^2+x_1*x_2-x_1*x_3+x_2*x_3+x_3^2-x_0*x_4+x_2*x_4+x_4^2,-x_1*x_2-x_2*x_3-x
      _0*x_4+x_1*x_4-x_2*x_4-x_4^2,x_0*x_1+x_0*x_3+x_1*x_3+x_2*x_3+x_3^2-x_0*x_4+x_2*x_4+x_3
      *x_4+x_4^2,x_0^2+x_0*x_1-x_0*x_2-x_0*x_3-x_1*x_3-x_2*x_3+x_3^2-x_0*x_4+x_2*x_4+x_3*x_4
      -x_4^2,x_0*x_2-x_0*x_3-x_1*x_3+x_2*x_3+x_3^2+x_1*x_4+x_2*x_4+x_3*x_4+x_4^2),
      ideal(-x_0*x_1+x_0*x_2-x_0*x_3-x_0*x_4+x_1*x_4-x_2*x_4+x_3*x_4-x_4^2,x_0*x_2+x_1*x_2+x
      _2^2-x_1*x_3-x_3^2+x_0*x_4+x_1*x_4+x_3*x_4+x_4^2,x_0*x_2+x_1*x_2+x_2^2-x_0*x_3-x_1*x_3
      +x_2*x_3+x_3^2-x_0*x_4-x_1*x_4-x_4^2,x_2^2-x_0*x_3+x_1*x_3-x_2*x_3+x_3^2+x_0*x_4-x_2*x
      _4-x_3*x_4+x_4^2,-x_0*x_1-x_1^2-x_1*x_2+x_0*x_3-x_1*x_3+x_2*x_3+x_0*x_4+x_1*x_4+x_2*x_
      4+x_3*x_4,-x_0*x_1-x_1^2-x_1*x_2+x_0*x_3-x_1*x_3+x_2*x_3-x_3^2+x_0*x_4+x_2*x_4+x_4^2,-
      x_1*x_2-x_0*x_3+x_1*x_3+x_2*x_3+x_3^2+x_0*x_4-x_1*x_4+x_3*x_4,x_0^2+x_0*x_1+x_0*x_2-x_
      0*x_3+x_1*x_3+x_3^2-x_0*x_4+x_1*x_4+x_2*x_4+x_3*x_4,x_0^2+x_0*x_1+x_0*x_2+x_0*x_3-x_1*
      x_3-x_2*x_3+x_3^2+x_0*x_4-x_3*x_4,x_0*x_2-x_1*x_3-x_2*x_3-x_3^2+x_0*x_4-x_1*x_4-x_2*x_
      4-x_3*x_4+x_4^2), ideal(-x_0*x_3+x_2*x_3-x_3^2+x_0*x_4-x_2*x_4,-x_1*x_2-x_2^2-x_1*x_3-
      x_2*x_3+x_3^2+x_0*x_4+x_1*x_4+x_2*x_4-x_4^2,x_0*x_3-x_0*x_4-x_4^2,x_0*x_2-x_1*x_2-x_2^
      2+x_0*x_3+x_2*x_3+x_0*x_4-x_2*x_4+x_4^2,x_1^2+x_1*x_2+x_0*x_3-x_1*x_3-x_2*x_3+x_3^2-x_
      1*x_4-x_2*x_4+x_3*x_4,x_1*x_3+x_3^2-x_1*x_4+x_2*x_4-x_3*x_4+x_4^2,-x_0*x_1+x_1^2-x_1*x
      _2+x_0*x_3+x_1*x_3-x_2*x_3-x_0*x_4-x_1*x_4-x_4^2,-x_0*x_1-x_0*x_2+x_1*x_3+x_2*x_3+x_3^
      2-x_0*x_4+x_1*x_4-x_2*x_4+x_4^2,x_0*x_3+x_1*x_3-x_2*x_3-x_3^2-x_0*x_4+x_1*x_4-x_2*x_4+
      x_4^2,x_0^2-x_0*x_1-x_0*x_2+x_0*x_3-x_1*x_3-x_2*x_3+x_3^2+x_0*x_4+x_3*x_4+x_4^2),
      ideal(x_2^2+x_0*x_3+x_1*x_3+x_2*x_3+x_3^2+x_0*x_4+x_1*x_4-x_2*x_4-x_3*x_4+x_4^2,x_0*x_
      2-x_1*x_2-x_0*x_3+x_1*x_3+x_1*x_4+x_2*x_4-x_3*x_4-x_4^2,x_0*x_2-x_0*x_3-x_1*x_3-x_2*x_
      3-x_3^2-x_0*x_4+x_1*x_4+x_2*x_4,-x_1*x_2-x_0*x_3-x_3^2+x_0*x_4-x_3*x_4-x_4^2,-x_0*x_1+
      x_1^2-x_0*x_3+x_1*x_3+x_2*x_3+x_3^2+x_3*x_4,-x_0*x_1+x_0*x_3-x_1*x_3+x_2*x_3-x_3^2+x_0
      *x_4-x_2*x_4-x_3*x_4-x_4^2,-x_0*x_1-x_1*x_3+x_3^2+x_0*x_4-x_1*x_4-x_3*x_4+x_4^2,x_0*x_
      2-x_2*x_3-x_3^2+x_0*x_4+x_1*x_4-x_2*x_4-x_3*x_4-x_4^2,x_0^2-x_0*x_1+x_0*x_3+x_1*x_3+x_
      3^2+x_0*x_4+x_1*x_4+x_2*x_4,x_0^2+x_0*x_3+x_1*x_3-x_2*x_3+x_0*x_4-x_1*x_4-x_2*x_4+x_3*
      x_4), ideal(x_1*x_3+x_2*x_3-x_3^2-x_2*x_4-x_3*x_4+x_4^2,x_0*x_2+x_1*x_2-x_2^2+x_2*x_3-
      x_3^2-x_0*x_4+x_2*x_4-x_4^2,x_1*x_2+x_0*x_3-x_1*x_3-x_2*x_3-x_3^2+x_1*x_4+x_2*x_4,-x_1
      *x_2-x_2^2+x_1*x_3+x_2*x_3-x_3^2-x_1*x_4+x_2*x_4+x_3*x_4-x_4^2,-x_0*x_1-x_1^2+x_1*x_2+
      x_2*x_3+x_3^2-x_1*x_4,-x_1^2-x_1*x_3-x_2*x_3-x_3^2-x_0*x_4+x_1*x_4+x_2*x_4-x_3*x_4-x_4
      ^2,x_1^2+x_1*x_2+x_0*x_3-x_2*x_3+x_3^2-x_4^2,x_0^2+x_0*x_1-x_0*x_2+x_0*x_3+x_0*x_4-x_1
      *x_4-x_4^2,x_0*x_1-x_0*x_3+x_1*x_3+x_2*x_3-x_3^2+x_0*x_4-x_2*x_4-x_4^2,-x_0*x_1-x_0*x_
      2+x_0*x_4+x_2*x_4-x_3*x_4+x_4^2),
      ideal(-x_1*x_2-x_2^2+x_0*x_3-x_3^2-x_0*x_4+x_1*x_4+x_3*x_4,x_0*x_2+x_2^2-x_0*x_3-x_1*x
      _3-x_3^2+x_1*x_4+x_2*x_4+x_3*x_4,-x_0*x_1-x_1^2-x_1*x_2+x_1*x_3-x_3^2-x_0*x_4-x_1*x_4-
      x_2*x_4,-x_1^2-x_1*x_2-x_1*x_3-x_2*x_3+x_3^2-x_1*x_4+x_2*x_4+x_3*x_4+x_4^2,x_1^2+x_1*x
      _2-x_0*x_3+x_3^2-x_0*x_4+x_1*x_4+x_2*x_4-x_4^2,-x_0*x_1-x_1*x_2+x_1*x_3+x_3^2+x_0*x_4-
      x_1*x_4-x_4^2,x_0^2+x_0*x_1+x_0*x_2+x_0*x_3+x_3^2+x_1*x_4-x_2*x_4,x_0*x_1+x_0*x_2+x_0*
      x_3+x_1*x_3+x_2*x_3+x_3^2-x_2*x_4+x_3*x_4+x_4^2,-x_0*x_1-x_0*x_2-x_0*x_3+x_1*x_3+x_2*x
      _3+x_0*x_4+x_1*x_4-x_2*x_4-x_3*x_4+x_4^2,x_0^2+x_0*x_2-x_0*x_3-x_1*x_3-x_2*x_3+x_3^2+x
      _0*x_4+x_2*x_4-x_4^2), ideal(x_1*x_3+x_2*x_3+x_3^2-x_0*x_4+x_1*x_4+x_2*x_4,-x_1*x_2-x_
      2^2-x_0*x_3+x_2*x_3-x_3^2-x_0*x_4-x_3*x_4-x_4^2,-x_0*x_3+x_1*x_3-x_3^2-x_0*x_4-x_1*x_4
      +x_3*x_4-x_4^2,-x_0*x_1-x_1^2+x_1*x_2+x_0*x_3+x_2*x_3-x_3^2+x_0*x_4+x_1*x_4+x_2*x_4+x_
      4^2,x_0*x_1-x_1^2-x_1*x_2+x_3^2-x_0*x_4-x_2*x_4-x_3*x_4,x_1^2+x_1*x_2+x_0*x_3-x_1*x_3+
      x_2*x_3+x_3^2-x_0*x_4+x_1*x_4-x_2*x_4-x_3*x_4-x_4^2,-x_1*x_3+x_3*x_4+x_4^2,x_0^2+x_0*x
      _1-x_0*x_2-x_0*x_3-x_1*x_3-x_3^2-x_1*x_4+x_3*x_4,-x_0^2+x_0*x_1+x_0*x_2+x_0*x_3-x_2*x_
      3+x_3^2-x_0*x_4+x_1*x_4+x_2*x_4+x_3*x_4+x_4^2,-x_0*x_1-x_0*x_2+x_0*x_3-x_1*x_3+x_2*x_3
      -x_3^2-x_0*x_4-x_1*x_4-x_3*x_4-x_4^2)};

tally apply(Mspecial1,M->minimalBetti M)

Mwith3syzs=select(Mspecial1, M->(fM =res M;rank fM_2==23))

elapsedTime specialSurf=apply(Mspecial1,M->surfaceFromModule(M));


sX2=select(smoothSurfaces,X->rank source gens X>12);
#sX2
Ms2=apply(sX2,X->moduleFromSurface X)
apply(Ms2,M->minimalBetti M)

betti(X=sX2_1)
minimalBetti X
X5= ideal (gens X)_{0..4};
	R=X5:X;
minimalBetti R, degree R, dim R
R8=ideal (gens R)_{0..7};
degree R8, dim R8, minimalBetti R8	
Ls=decompose (R8:R)
apply(Ls,L->(degree L, dim L, minimalBetti L, degree(X+L)))
(dim R, degree R, degree(R+X), dim (R+X))
cR=decompose R
apply(cR,c->(dim c, degree c, degree(c+X), dim(c+X)))
fX=res X
omegaX=trim Ext^1(X,P4^{-5})
minimalBetti omegaX
P9=kk[y_0..y_9]
P4xP9=P4**P9
graph=sub(vars P9,P4xP9)*sub(presentation omegaX,P4xP9)
pL=sub(diff(sub(transpose vars P4,P4xP9),graph),P9);
Y=ann coker pL;

minimalBetti Y
codim Y, degree Y
while(
    ls=apply(3,i-> random(kk^1,kk^(numgens ring X)));
    Hs= sum(ls, l-> ideal(vars ring X*transpose l));
    dim(Hs+X)=!=0) do ()

Hs1=saturate sum(ls,l->ann(coker (transpose syz l*pL)));
degree Hs1, dim Hs1, minimalBetti Hs1
--intersection matrices
matrix{{11,7},{7,-6}}, matrix{{19,1},{1,-6+2}}

fY=res(Y,FastNonminimal=>true)
degree Y
betti fY
omegaY=image(syz transpose fY.dd_8)/image(transpose fY.dd_7);
m11x70=presentation prune omegaY
P10=kk[z_0..z_10]
P9xP10=P9**P10
betti(graph2=sub(vars P10,P9xP10)*sub(m11x70,P9xP10))
betti(pL2=map(P10^10,,sub(diff(sub(transpose vars P9,P9xP10),graph2),P10)))
Z=ann coker pL2;
minimalBetti Z
degree Z

while(
    ls=apply(3,i-> random(kk^1,kk^(numgens ring Y)));
    Hs= sum(ls, l-> ideal(vars ring Y*transpose l));
    dim(Hs+Y)=!=0) do ()

Hs2=saturate sum(ls,l->ann(coker (transpose syz l*pL2)));
degree Hs2, dim Hs2, minimalBetti Hs2



matrix{{19,1},{1,-4}},matrix{{17,-3},{-3,-1}}

fZ=res(Z,FastNonminimal=>true)
minimalBetti Z
betti fZ
codim Z
degree Z
betti(omegaZ=prune coker transpose fZ.dd_8)
m8x56=presentation omegaZ;

P7=kk[w_0..w_7]
P10xP7=P10**P7
betti(graph3=sub(vars P7,P10xP7)*sub(m8x56,P10xP7))
betti(pL3=map(P7^11,,
	sub(diff(sub(transpose vars P10,P10xP7),graph3),P7)
	))

W=ann coker pL3;
minimalBetti W
dim W, degree W

matrix{{17,-3},{-3,-1}}
while(
    ls=apply(3,i-> random(kk^1,kk^(numgens ring Z)));
    Hs= sum(ls, l-> ideal(vars ring Z*transpose l));
    dim(Hs+Z)=!=0) do ()

Hs3=saturate sum(ls,l->ann(coker (transpose syz l*pL3)));
degree Hs3, dim Hs3, minimalBetti Hs3

matrix{{10,-4},{-4,1}},matrix{{3,-3},{-3,3}}

betti(fW=res(W,FastNonminimal=>true))
betti(omegaW=prune (image(syz transpose fW.dd_6)/image(transpose fW.dd_5)))
P3=kk[u_0..u_3]
P7xP3=P7**P3
betti(graph4=sub(vars P3,P7xP3)*sub(presentation omegaW,P7xP3))
betti(pL4=map(P3^8,,
	sub(diff(sub(transpose vars P7,P7xP3),graph4),P3)
	))

U=ann coker pL4;
minimalBetti U, degree U, dim U
while(
    ls=apply(3,i-> random(kk^1,kk^(numgens ring W)));
    Hs= sum(ls, l-> ideal(vars ring W*transpose l));
    dim(Hs+W)=!=0) do ()
Hs4=saturate sum(ls,l->ann(coker (transpose syz l*pL4)));
degree Hs4, dim Hs4, minimalBetti Hs4


degree Hs1, degree Hs2, degree Hs3, degree Hs4

--(15;5^6,4^2,3^2,2^3,1^2)
binomial(15+2,2)-6*binomial(5+1,2)-
2*binomial(4+1,2)-2*binomial(3+1,2)-3*binomial(2+1,2)-2==5-2
15^2-6*5^2-2*4^2-2*3^2-3*2^2-2==11
---

degree Hs3, dim Hs3, minimalBetti Hs3
matrix{{17,-3},{-3,-3}}
matrix{{9,-5},{-5,-2}}


minimalBetti(R3=R:R6)
degree R3, dim R3

Ms=apply(smoothSurfaces,X->moduleFromSurface X);
tally apply(Ms,M-> minimalBetti M)

sixSecantLines=method()
sixSecantLines(Ideal) := X-> (
    X5=ideal (gens X)_{0..4};
    betti(secants=X5:X);
    secants)
minimalBetti X
betti(J=sixSecantLines X)
dim J, degree J
minimalBetti J
cJ=decompose J
apply(cJ,c->(degree c, dim c, minimalBetti c))
intersect cJ ==J
tally apply(cJ,c->(dim(c+X),degree(c+X)))

    minimalB
elapsedTime singX:=X+minors(2,jacobian X);
elapsedTime dim saturate singX
-- => X is a smooth surface
degree X, genera X

-- adjunction process 
elapsedTime omegaX=Ext^1(module X,P4^{-5})
betti res omegaX

P9=kk[y_0..y_9]
P4xP9=P4**P9
graph=sub(vars P9,P4xP9)*sub(presentation omegaX,P4xP9);
betti(presL=contract(transpose sub(vars P4,P4xP9),graph))
betti(presL=map(P9^5,,sub(contract(transpose sub(vars P4,P4xP9),graph),P9)))


--The first adjoint surface
X1=ann coker presL;
minimalBetti X1, codim X1, dim X1, degree X1

-- How many (-1) lines are there on X?

H0=ann coker sub(contract(transpose sub((vars P4)_{1,2,3,4},P4xP9),graph),P9);
minimalBetti H0
H1=ann coker sub(contract(transpose sub((vars P4)_{0,2,3,4},P4xP9),graph),P9);
H2=ann coker sub(contract(transpose sub((vars P4)_{0,1,3,4},P4xP9),graph),P9);
degree (H0+H1+H2)==5
assert(dim (X+ideal (vars P4)_{0,1,2})==0)
-- => conclude there are 5 (-1) lines.

-*
--Intersection matrix of X
--H^2 H.K   is   11 7
--H.K K^2        7 -6
matrix{{11,7},{7,-6}}
--=>
--H1^2 H1.K1  is 19 1
--H1.K1 K1^2     1 -1
matrix{{19,1},{1,-1}}
*-

elapsedTime betti(fX1=res(X1,FastNonminimal=>true))
minimalBetti X1
elapsedTime betti (fX1=res X1)  -- 59.6388 seconds elapsed

P10=kk[z_0..z_10]
P9xP10=P9**P10
graph1=sub(vars P10,P9xP10)*sub(transpose fX1.dd_7,P9xP10);
presL1=sub(diff(transpose sub(vars P9,P9xP10),graph1),P10);
betti(X2=ann coker presL1)
degree X2, genera X2
minimalBetti X2

L3=subsets(toList(0..9),3)
L3good=select(L3,L->dim(X1+ideal (vars P9)_L)==0)
genera X1, genera X2
L=first L3good
Hs=apply(L,i-> (Li=select(toList(0..9),j->j!=i);
    ann coker sub(contract(transpose sub((vars P9)_Li,P9xP10),graph1),P10)));
degree sum Hs==1

-*
--There is one (-1)-line on X1 =>
--H2^2 H2.K2  is 20 0
--H2.K2 K2^2     0  0
matrix{{20,0},{0,0}}
-- Hodge Index K2 is numerically trivial, pg=q=0 =>
-- X2 is a minimal Enriques surface
-- H=H2-sum_1^5 2E_i - E_6
*-
minimalBetti X2

elapsedTime tally apply(10,i-> (X=findSurface P4;
	J=sixSecantLines X;
	(dim J, degree J))) -- 83.9146 seconds elapsed


--The random search lead to 50 good Ms
-- Some example:

toString Ms2

use P4
Ms={ideal(-x_1*x_3-x_2*x_3,-x_0*x_2+x_1*x_2-x_2^2+x_0*x_3+x_2*x_3-x_3^2+x_0*x_4+x_4^2,x_0*x_2
      +x_1*x_2+x_2^2+x_1*x_3-x_2*x_3-x_3^2-x_0*x_4-x_1*x_4+x_2*x_4+x_3*x_4-x_4^2,x_1*x_2+x_2^2+x
      _0*x_3-x_1*x_3+x_2*x_3-x_3^2+x_0*x_4-x_1*x_4-x_2*x_4+x_3*x_4-x_4^2,x_0*x_1-x_1^2+x_1*x_2-x
      _0*x_3+x_2*x_3-x_3^2+x_1*x_4+x_2*x_4+x_3*x_4+x_4^2,-x_0*x_1-x_1^2-x_1*x_2-x_3^2,-x_1^2-x_1
      *x_2+x_0*x_3+x_1*x_3+x_3^2-x_3*x_4+x_4^2,-x_0^2+x_0*x_1-x_0*x_2-x_2*x_3+x_3^2+x_0*x_4-x_1*
      x_4-x_2*x_4-x_3*x_4,x_0^2+x_0*x_1+x_0*x_2-x_0*x_3+x_2*x_3+x_3*x_4,x_0*x_1+x_0*x_2-x_1*x_3-
      x_2*x_3+x_0*x_4+x_2*x_4+x_3*x_4+x_4^2),
      ideal(-x_0*x_3+x_1*x_3+x_2*x_3+x_3^2-x_0*x_4+x_1*x_4+x_2*x_4-x_3*x_4-x_4^2,x_0*x_2+x_1*x_2
      +x_0*x_3-x_3^2+x_1*x_4-x_2*x_4+x_3*x_4,x_0*x_2-x_1*x_2+x_2^2+x_0*x_3-x_1*x_3+x_2*x_3-x_0*x
      _4-x_2*x_4-x_3*x_4,x_0*x_2-x_1*x_2-x_2^2-x_0*x_3+x_1*x_3-x_2*x_3-x_3^2-x_1*x_4-x_2*x_4-x_4
      ^2,-x_0*x_1-x_1^2-x_0*x_3+x_2*x_3-x_1*x_4-x_4^2,-x_0*x_1+x_1^2-x_1*x_2-x_0*x_3+x_2*x_3-x_3
      ^2-x_0*x_4+x_2*x_4+x_3*x_4-x_4^2,-x_0*x_1+x_1^2+x_1*x_2-x_0*x_3-x_1*x_3-x_0*x_4-x_1*x_4-x_
      3*x_4,x_0^2+x_0*x_1-x_2*x_3+x_3^2+x_0*x_4-x_1*x_4-x_2*x_4-x_3*x_4+x_4^2,x_0^2-x_0*x_1+x_0*
      x_2+x_3^2-x_1*x_4+x_3*x_4+x_4^2,x_0^2-x_0*x_1-x_0*x_2+x_0*x_3-x_1*x_3+x_2*x_3+x_3^2-x_1*x_
      4+x_3*x_4+x_4^2), ideal(-x_2*x_3-x_3^2-x_0*x_4+x_1*x_4+x_3*x_4-x_4^2,-x_0*x_2+x_2^2+x_0*x_
      3+x_1*x_3-x_2*x_4,-x_1*x_2+x_2^2-x_0*x_3+x_1*x_3+x_2*x_3+x_3^2-x_1*x_4-x_3*x_4-x_4^2,-x_1*
      x_2-x_2^2-x_0*x_3-x_1*x_3+x_2*x_3+x_3^2+x_2*x_4-x_4^2,x_0*x_1-x_1*x_2-x_0*x_3-x_1*x_3-x_2*
      x_3+x_3^2-x_0*x_4-x_2*x_4-x_3*x_4,x_1^2-x_1*x_2-x_0*x_3-x_1*x_3-x_1*x_4-x_2*x_4-x_3*x_4+x_
      4^2,x_1^2+x_1*x_2-x_0*x_3+x_1*x_3-x_2*x_3-x_3^2-x_0*x_4-x_1*x_4-x_2*x_4-x_3*x_4+x_4^2,-x_0
      ^2+x_0*x_2+x_1*x_3-x_2*x_3+x_3^2-x_0*x_4-x_1*x_4+x_2*x_4+x_3*x_4+x_4^2,-x_0*x_1+x_0*x_2-x_
      0*x_3+x_1*x_3-x_0*x_4+x_2*x_4-x_3*x_4-x_4^2,-x_0*x_1-x_0*x_2+x_0*x_3+x_1*x_3+x_2*x_3-x_3^2
      +x_1*x_4+x_2*x_4-x_4^2), ideal(-x_0*x_1+x_1*x_2+x_0*x_3+x_1*x_3-x_2*x_3-x_3^2+x_0*x_4+x_1*
      x_4+x_3*x_4,x_0*x_1-x_1*x_2-x_1*x_3-x_3^2-x_1*x_4-x_2*x_4+x_3*x_4-x_4^2,x_0*x_1-x_1*x_2-x_
      0*x_3+x_2*x_3-x_1*x_4+x_2*x_4+x_3*x_4,x_0*x_2-x_2^2-x_0*x_3+x_1*x_3+x_2*x_3+x_3^2-x_0*x_4+
      x_1*x_4-x_2*x_4-x_4^2,-x_0*x_2+x_1*x_2-x_0*x_3+x_1*x_3+x_2*x_3-x_0*x_4-x_3*x_4-x_4^2,-x_1*
      x_2-x_2^2-x_0*x_3-x_3^2-x_2*x_4,x_0*x_1-x_1^2-x_0*x_3-x_1*x_3-x_2*x_3+x_0*x_4-x_1*x_4+x_2*
      x_4-x_4^2,x_1^2+x_1*x_2+x_1*x_3+x_2*x_3+x_3^2+x_2*x_4+x_3*x_4-x_4^2,-x_0^2+x_0*x_1-x_1*x_3
      +x_2*x_3+x_0*x_4,-x_0*x_1-x_0*x_2+x_0*x_3+x_2*x_3+x_0*x_4+x_2*x_4-x_3*x_4+x_4^2),
      ideal(-x_0*x_1-x_1^2+x_1*x_2-x_0*x_4-x_2*x_4+x_3*x_4,x_0*x_2+x_1*x_2-x_2^2-x_0*x_3+x_1*x_3
      -x_2*x_3-x_0*x_4+x_1*x_4+x_3*x_4-x_4^2,x_1*x_2+x_2^2-x_2*x_3+x_0*x_4+x_1*x_4-x_
       2*x_4-x_3*x_4+x_4^2,-x_0*x_2+x_0*x_3-x_1*x_3+x_2*x_3-x_0*x_4-x_2*x_4-x_3*x_4-x_4^2,-x
       _0*x_1-x_1*x_2-x_0*x_3+x_1*x_3-x_3^2+x_1*x_4-x_2*x_4,-x_1^2-x_1*x_2-x_0*x_3+x_2*x_3+x
       _3^2+x_0*x_4+x_2*x_4-x_3*x_4+x_4^2,x_0*x_1+x_1*x_3+x_0*x_4-x_2*x_4-x_4^2,x_0^2+x_0*x_
       2-x_0*x_3+x_1*x_3-x_3^2+x_0*x_4-x_3*x_4,x_0*x_1+x_0*x_2+x_0*x_3-x_1*x_3+x_2*x_3+x_3^2
       -x_3*x_4,-x_0^2-x_0*x_3-x_1*x_3+x_2*x_3+x_3^2+x_1*x_4+x_2*x_4+x_3*x_4+x_4^2),
       ideal(-x_0*x_3+x_1*x_3-x_2*x_3+x_0*x_4-x_1*x_4+x_2*x_4+x_4^2,x_0*x_2+x_2^2-x_0*x_3+x_
       1*x_3+x_2*x_3-x_0*x_4+x_3*x_4+x_4^2,x_1*x_2+x_0*x_3-x_1*x_3+x_2*x_3-x_3^2-x_0*x_4+x_1
       *x_4+x_2*x_4+x_3*x_4+x_4^2,-x_0*x_2+x_1*x_2+x_2^2-x_1*x_3+x_2*x_3-x_3^2-x_0*x_4-x_2*x
       _4-x_3*x_4-x_4^2,-x_0*x_1-x_1*x_2-x_0*x_3+x_2*x_3+x_0*x_4-x_1*x_4+x_2*x_4-x_3*x_4-x_4
       ^2,-x_1^2-x_0*x_3-x_2*x_3-x_3^2-x_1*x_4-x_2*x_4+x_3*x_4+x_4^2,x_0*x_1-x_1^2-x_1*x_2-x
       _0*x_3+x_3^2+x_0*x_4-x_1*x_4-x_2*x_4+x_3*x_4+x_4^2,x_0^2+x_0*x_2+x_0*x_3+x_1*x_3-x_3^
       2-x_1*x_4-x_2*x_4-x_3*x_4-x_4^2,x_0*x_1+x_0*x_3-x_1*x_3+x_3^2+x_0*x_4+x_2*x_4+x_3*x_4
       +x_4^2,-x_0^2+x_0*x_1+x_0*x_2-x_0*x_3-x_2*x_3+x_3^2-x_0*x_4-x_1*x_4),
       ideal(-x_0*x_1-x_1*x_2-x_0*x_3+x_1*x_3-x_2*x_3+x_3^2+x_0*x_4+x_2*x_4-x_4^2,x_0*x_2+x_
       2^2-x_1*x_3+x_2*x_3-x_0*x_4-x_1*x_4+x_2*x_4-x_3*x_4-x_4^2,x_1*x_2-x_2*x_3+x_0*x_4-x_1
       *x_4+x_4^2,x_0*x_2+x_1*x_2-x_2^2-x_0*x_3+x_2*x_3+x_3^2+x_0*x_4-x_1*x_4-x_2*x_4-x_3*x_
       4,x_0*x_1+x_1^2-x_1*x_2+x_0*x_3+x_1*x_3-x_2*x_3-x_1*x_4+x_3*x_4+x_4^2,-x_1^2-x_1*x_3+
       x_1*x_4+x_3*x_4-x_4^2,-x_0*x_1-x_1^2+x_1*x_2-x_0*x_3-x_1*x_3+x_2*x_3-x_0*x_4+x_1*x_4-
       x_2*x_4-x_4^2,-x_0^2-x_0*x_1+x_0*x_2-x_0*x_3+x_1*x_3-x_0*x_4-x_1*x_4-x_4^2,x_0*x_1-x_
       0*x_3+x_1*x_3+x_2*x_3+x_3^2-x_1*x_4+x_2*x_4-x_3*x_4-x_4^2,x_0^2+x_0*x_1-x_0*x_2-x_0*x
       _3-x_2*x_3+x_3^2+x_0*x_4-x_2*x_4-x_3*x_4+x_4^2)};
#Ms
tally apply(Ms,M->minimalBetti M)

minimalBetti(M=Ms_4)
betti (fM=res(M))
rows=positions(degrees fM_3,d->d=={4})
columns=positions(degrees fM_2,d->d=={3})
betti (N=(fM.dd_3)^columns_rows)
while(
  while(
    while(n1=random(kk^(rank source N),kk^2);
	N2=map(P4^{15:-3},,N*n1);
    not (dim coker transpose N2==0)) do();
    m10x10=(fM.dd_2_{0..14}*syz transpose syz(transpose N2,DegreeLimit=>-3));
    betti(sm10x10=syz transpose m10x10);
    betti(X=trim ideal((transpose sm10x10)*fM.dd_2));
  not(degree X ==11 and dim X==3)) do ();
  singX=X+minors(2,jacobian X);
elapsedTime dim singX !=0) do()

dim singX
minimalBetti X
degree X
apply(Ms, M-> (betti(X=surfaceFromModule M);
	 J=sixSecantLines X;
	 (degree J, dim J)))
--=> there are at least 4 different families, they differ
--   by the structure of their 6-secant lines.
-- The search lead to the altogether 50 examples.
--
-- The time from computing (11,15,12,1) new examples, i.e.,
-- from (3, 9, 8, 1) examples to (14, 24, 20, 2) examples
-- took 8877.85 seconds.
8877.85/60/21 --minutes per example on average

M=last Ms
minimalBetti M
betti(X=surfaceFromModule M)
betti(J=sixSecantLines X)
-- Fact: if finite, then
-- the number 6-secant lines + number of (-1) lines == 10
-- by Le Barz (1981) secant formula
dim J==3
cJ=decompose J
netList apply(cJ,c->(dim c, degree c, minimalBetti c, degree (c+X), dim (c+X)))
cJ1X=decompose (first cJ+X);
netList apply(cJ1X,c->(dim c, degree c, minimalBetti c, degree radical (c+X), dim (c+X)))
-- the first component of J which is a plane intersects X
-- in a plane quartic curve and three points 
-- the 3 lines through two points of X in the plane
-- are 6-secants 
-- => there are 4+3=7 six secant lines,
-- => the plane is contained in the intersection of
--    the five cubic generators of X
-- => there should be three (-1) lines


betti (fX=res X)
elapsedTime omegaX=Ext^1(module X,P4^{-5})
betti res omegaX

P9=kk[y_0..y_9]
P4xP9=P4**P9
graph=sub(vars P9,P4xP9)*sub(presentation omegaX,P4xP9);
betti(presL=contract(transpose sub(vars P4,P4xP9),graph))
betti(presL=map(P9^5,,sub(contract(transpose sub(vars P4,P4xP9),graph),P9)))


--The first adjoint surface
X1=ann coker presL;
minimalBetti X1, codim X1, dim X1, degree X1

-- How many (-1) lines does X have?
L3=subsets(toList(0..4),3)
L3good=select(L3,L->dim(X+ideal (vars P4)_L)==0)
L=first L3good
H0=ann coker sub(contract(transpose sub((vars P4)_{1,2,3,4},P4xP9),graph),P9);
minimalBetti H0
H1=ann coker sub(contract(transpose sub((vars P4)_{0,2,3,4},P4xP9),graph),P9);
H2=ann coker sub(contract(transpose sub((vars P4)_{0,1,2,4},P4xP9),graph),P9);
(dim(H0+H1+H2),degree (H0+H1+H2))==(1,3) -- as expected

minimalBetti X1
--betti(fX1=res X1)
betti(fX1=res(X1,FastNonminimal=>true))

P10=kk[z_0..z_10]
P9xP10=P9**P10
graph1=sub(vars P10,P9xP10)*sub(transpose fX1.dd_7,P9xP10);
presL1=sub(diff(transpose sub(vars P9,P9xP10),graph1),P10);
betti(X2=ann coker presL1)
degree X2, genera X2, minimalBetti X2

L3=subsets(toList(0..9),3)
L3good=select(L3,L->dim(X1+ideal (vars P9)_L)==0)
L=first L3good
Hs=apply(L,i-> (Li=select(toList(0..9),j->j!=i);
    ann coker sub(contract(transpose sub((vars P9)_Li,P9xP10),graph1),P10)));
(dim sum Hs,degree sum Hs) == (1,2)
-- intersection matrices
matrix{{11,7},{7,-6}}, matrix{{19,1},{1,-6+3}}, matrix{{18,-2},{-2,-1}}
S=ZZ[l_1,l_2,l_3,l_4,l_5]
matrix{{13,-3},{-3,-1+l_3}}
--
minimalBetti X2
betti (fX2=res(X2,FastNonminimal=>true))

P8=kk[w_0..w_8]
P10xP8=P10**P8
graph2=sub(vars P8,P10xP8)*sub(transpose fX2.dd_8 ,P10xP8);
presL2=sub(diff(transpose sub(vars P10,P10xP8),graph2),P8);
betti(X3=ann coker presL2)
degree X3, genera X3, minimalBetti X3

L3=subsets(toList(0..10),3);
L3good=select(L3,L->dim(X2+ideal (vars P10)_L)==0);
L=first L3good
Hs=apply(L,i-> (Li=select(toList(0..10),j->j!=i);
    ann coker sub(contract(transpose sub((vars P10)_Li,P10xP8),graph2),P8)));
dim sum Hs==0
-- intersection matrix
matrix{{13,-3},{-3,-1}}, matrix{{6,-4},{-4,-1+l_4}}
minimalBetti X3
betti(fX3=res(X3))
P5=kk[u_0..u_5]
P8xP5=P8**P5

graph3=sub(vars P5,P8xP5)*sub(transpose fX3.dd_6,P8xP5);
presL3=sub(diff(transpose sub(vars P8,P8xP5),graph3),P5);
betti(X4=ann coker presL3)
degree X4, genera X4, minimalBetti X4

L3=subsets(toList(0..8),3)
L3good=select(L3,L->dim(X3+ideal (vars P8)_L)==0)
L=first L3good
Hs=apply(L,i-> (Li=select(toList(0..8),j->j!=i);
    ann coker sub(contract(transpose sub((vars P8)_Li,P8xP5),graph3),P5)));
(dim sum Hs, degree sum Hs)==(1,3)
matrix{{6,-4},{-4,-1+3}}, matrix{{0,-2},{-2,2+l_5}}
betti(fX4 =res X4)
-- => X4 is the intersection of a P1xP2
--    defined by the 3x2 matrix with a quadric
-- In terms of bihomogeneous coordinates on P1xP2
-- the quadric is given by a polynomial
-- of bi-degree (2,2). The corresponding quadratic form
-- is described by a 3x3 matrix of quadrics on P1 hence
-- has a discriminat of degree 6.
P1xP2=kk[s_0..s_1,t_0..t_2,Degrees=>{2:{1,0},3:{0,1}}]
mst=matrix apply(3,i->apply(2,j->s_j*t_i))
P5xP1xP2=P5**P1xP2
m3x2=fX4.dd_2^{1..3}_{0,1}
sub(m3x2,P5xP1xP2)-sub(mst,P5xP1xP2)
para=ideal gens gb ideal(sub(m3x2,P5xP1xP2)-sub(mst,P5xP1xP2))
Qst=trim ideal (sub(gens X4,P5xP1xP2)%para)
Q=sub(Qst,P1xP2)
tt=(vars P1xP2)_{2..4}
hess=diff(transpose tt,diff(tt,gens Q))
cDisc=decompose ideal det hess
use P1xP2
saturate(cDisc_0+Q,ideal s_1)
decompose saturate(cDisc_0+Q,ideal s_1)
-- to pass to minimal surface we need a field extension
betti(tenLines=saturate(saturate(cDisc_1+Q,ideal(s_0,s_1)),ideal(t_0..t_2)))
#decompose tenLines

--extension to charcteristic zero

betti( fM=res Ms_0)
mons=flatten entries sub(basis(2,P4/ideal fM.dd_1),P4)
def1=flatten apply(10,i->apply(mons,m->matrix{apply(10,j->
		if j==i then m else 0_P4)}))
d=first def1
	betti (d2=d*fM.dd_2//fM.dd_1)
	betti (d3=d2*fM.dd_3//fM.dd_2)
	d3^{15..21}_{0,1}

T=kk[t_0..t_49]
m7x2=sum(50, i-> (d=def1_i;
	betti (d2=d*fM.dd_2//fM.dd_1);
	betti (d3=d2*fM.dd_3//fM.dd_2);
	T_i*sub(d3^{15..21}_{0,1},T)))
leadTerm mingens trim ideal m7x2

-- => the goodMs as a subset of allMs have codimension 14
--    at the given point, hence dimension 50-14=36.
-- (modulo PGL(5) there is a 36-24=12-dimensional family)
12 == 15*2-5*2-8
-- the same count for the family of abstract surfaces:
--   15*2 parameters for the point
--   h^0(O_X(1))*h^1(O_X(1))=5*2 conditions on the points
--   8=dim PGL(3)
--
-- Enriques family:
10+6*2-5*2==12

-- Choose 36 linear forms in ZZ[t_1,...,t_50]
-- which intersect mod 3 in precisely the given point M
-- Conclude: there exists a number field K and a prime pp
-- such that O_K/pp = ZZ/3 and a familily of module M over
-- an open part of Spec O_K, which extends the given module M
-- and the surface X to a family od surface.

apply(Ms,M-> (fM=res M;
	mons=flatten entries sub(basis(2,P4/ideal fM.dd_1),P4);
	def1=flatten apply(10,i->apply(mons,m->matrix{apply(10,j->
			if j==i then m else 0_P4)}));
	m7x2=sum(50, i-> (d=def1_i;
		betti (d2=d*fM.dd_2//fM.dd_1);
		betti (d3=d2*fM.dd_3//fM.dd_2);
		T_i*sub(d3^{15..21}_{0,1},T)));
	rank source mingens ideal m7x2==14))
--=> all 4 surfaces lift to characteristic zero

betti (fM=res M)
T=kk[t_0..t_49]
mons=flatten entries sub(basis(2,P4/ideal fM.dd_1),P4);
	def1=flatten apply(10,i->apply(mons,m->matrix{apply(10,j->
			if j==i then m else 0_P4)}));
	m3x3=sum(50, i-> (d=def1_i;
		betti (d2=d*fM.dd_2//fM.dd_1);
		betti (d3=d2*fM.dd_3//fM.dd_2);
		T_i*sub(d3^{15..22}_{0,1,2},T)));
	tcd=rank source mingens ideal m3x3
dimG=50
50-tcd+2-24
15*2-10-8
