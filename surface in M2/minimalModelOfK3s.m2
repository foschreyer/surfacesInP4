
 -*
(degree, sectionalGenus, number of points blownup, s=h^1(O_X(1)), genus of polarization)
candidatesWithGenus={
    (7, 5, 1, 0, 5),
    (8, 6, 1, 0, 7),
    (9, 8, 5, 1, 8),
    (10, 9, 3, 1, 15),
    (11, 11, 5, 2, 21),
    (11, 11, 5, 2, 18),
    (11, 11, 5, 2, 16),
    (11, 11, 5, 2, 15),
    (11, 12, 10, 3, 13),
    (12, 14, 11, 4, 20)}
*-


-- case (10, 9, 3, 1, 15) -- most likely is not dominant
restart
needsPackage"NongeneralTypeSurfacesInP4"
kk=ZZ/nextPrime (10^4);P4=kk[x_0..x_4];E=kk[e_0..e_4,SkewCommutative=>true];
setRandomSeed("fix very good decomposition of D");-- works
--viewHelp "NongeneralTypeSurfacesInP4"

minimalBetti(X=K3surfaceD10S9L1 P4)
elapsedTime betti(Y=minimalModelOfK3(X,Verbose=>true))  -- 339.883s elapsed
-*
time to compute the canonical divisor:
 -- 5.84334s elapsed
time to decompose the canonical divisor:
 -- .45341s elapsed
multilicities of canonical divisor = {1, 1, 4}
genus of the minimal model = 15
time to compute the minimal model:
 -- 321.414s elapsed
                                   0  1
genus = 15, betti numbers = total: 1 78
                                0: 1  .
                                1: . 78
*-
P15=ring Y
L=ideal((gens P15)_{0..4})
betti(X'=trim ker map(P15/Y,P4,gens L))
X==X'
pts=primaryDecomposition(Y+L);#pts
netList apply(pts,c->(dim c, degree c, betti c))
Es=apply(pts,c->(p=radical c;ker map(P15/p,P4,gens L)));
D=canonicalDivisor X;
cD=decompose D;
netList apply(cD,E->(dim E,degree E, betti E))
betti (H=intersect cD_{0,1})
cH=decompose (X+(ideal H_0));#cH
netList apply(cH,h->(dim h, degree h, betti h))
kk2=GF(char kk,2)
P4'=kk2[gens P4]
AB=decompose sub(cH_2,P4');#AB
tally apply(AB,c->(dim c, degree c, betti c))
betti (sixSec=trim sum(AB))
dim sixSec, degree sixSec
radical sixSec
sixSecLine=ideal (gens P4')_{2..4}
degree (sixPts=trim (sixSecLine+sub(X,P4')))
fourPts=sixPts:sixSec;
degree fourPts
tally apply(decompose sixPts,c->(dim c, degree c, betti c))

-* -- study of (4,5) linked surface *-

ci=ideal(gens X*random(source gens X,P4^{-4,-5}));
minimalBetti(Z=ci:X)
dim Z, degree Z, sectionalGenus Z, genera Z
betti tateResolutionOfSurface Z
betti tateResolutionOfSurface X
betti(fX=res X)
betti (singX0=saturate ideal jacobian ideal X_0)

L=trim ideal fX.dd_2^{10}_{15..17}
betti(s1=saturate(singX0,L))
dim s1, degree s1
betti(s2=saturate(singX0,s1))
dim s2,degree s2
betti(s3=s2:L)
s3==saturate(X+L)
-- => the quartic is singular along the line L with transversal A1-singularities
--    and pinch points at the 6 intersection points of the secant line L with X
saturate ideal singularLocus(P4/Z)==L
minimalBetti(C=saturate(Z+X)) -- the intersection curve
dim C, degree C, genus C
saturate(C,L)==C
betti(C1=(ideal(C_0,C_1)+X):C) -- turns out to be the canonical divisor
dim C1, degree C1, genus C1
netList apply(cC1=decompose C1,d->(dim d, degree d, genus d))
H=ideal (intersect(cC1_0,cC1_1))_0
H1=saturate(((H+X):cC1_0):cC1_1);
dim H1, degree H1, sectionalGenus H1, betti H1
H1==H1+X
ideal(H1_0,H1_1)
minimalBetti cC1_2
dim (cC1_2+H1),degree (cC1_2+H1)
H2=ideal(gens cC1_2*random(source gens cC1_2,P4^{-2}))
betti(H2a=(X+H2):cC1_2)

--cC=decompose C;#cC
betti (E2=intersect(cC1))
H3=ideal(gens E2*random(source gens E2,P4^{-3}));
betti(E3=(X+H3):E2)
degree E3
elapsedTime D=canonicalDivisor X; -- 5.84683s elapsed
--C1==D
selfIntersectionNumber(X,D)
elapsedTime tally apply(cD=decompose D,c->(dim c, degree c, genus c))
(d,sg) =(degree X, sectionalGenus X)
HdotK(d,sg)==6
Ksquare(d,sg,2)==-3
R5=residualInQuintics X; dim R5, degree R5, degree (R5+X)
LeBarzN6(d,sg,2)==3
pd={1,1,4}
polarizationDegree=d+sum(pd,k->k^2)
polGenus=sub((polarizationDegree+2)/2,ZZ)
netList apply(cD,c->(dim c, degree c, genus c))
betti(sD2=saturate(X+cD_2^4))
betti(sD1=saturate(X+cD_1^4))
degree sD2
betti (D1=intersect(sD2,cD_0,cD_1))
betti (D1=intersect(sD1,cD_0))
betti(H5=ideal(gens D1*random(source gens D1,P4^{-5})))
betti(residual=(X+H5):D1)
degree residual
betti (res1=trim ideal((gens residual)%X))
betti (H6=trim ideal( (gens intersect((ideal vars P4)^6,res1))%X))
betti(h6a=gens trim ideal (((gens H6))%(X+H5)))
betti (h6b=map(P4^1,,vars P4*H5_0))
P15=kk[y_0..y_15]
elapsedTime betti(Y=trim ker map(P4/X,P15, h6b|h6a))  -- 313.096s elapsed

elapsedTime betti(TX= tateResolutionOfSurface X)

elapsedTime(dim Y, degree Y, genera Y)

degrees ring Y
degrees P15
elapsedTime betti(fY=resolution(Y,DegreeLimit=>2,LengthLimit=>3))
-- 660.072s elapsed for Length 2

L4=ideal(y_0..y_4)
betti(pts1=saturate (L4+Y))
degree pts1, dim pts1
elapsedTime pts=apply(cD,c->(elapsedTime p=trim ker map(P4/c,P15, h6b|h6a);
	<< betti p <<endl;p));
netList apply(pts, p-> transpose syz transpose sub(jacobian p,kk))	
tally apply(cpts1=decompose pts1,c->betti c)
cpts1
-- Experiment: Is every point on X possible for the 4p condition?:
p=first cpts1
betti(sp4=saturate(p^4+Y))
--betti(H1=ideal(gens sp4*random(source gens sp4,P15^{-1}))
h5=(gens sp4)_{0..5}
P5=kk[z_0..z_5]
elapsedTime betti(Z=trim ker map(P15/Y,P5,h5))
minimalBetti Z
betti(fZ=res Z)
prune (ker transpose fZ.dd_5/image transpose fZ.dd_4)

p=last cpts1
betti(sp4=saturate(p^4+Y))
--betti(H1=ideal(gens sp4*random(source gens sp4,P15^{-1}))
h5=(gens sp4)_{0..5}
P5=kk[z_0..z_5]
elapsedTime betti(Z=trim ker map(P15/Y,P5,h5))
minimalBetti Z
betti(fZ=res Z)
singPtZ=prune (ker transpose fZ.dd_5/image transpose fZ.dd_4)
h4=presentation singPtZ
minimalBetti(X'=trim ker map(P5/Z,P4,h4))
singX'=ideal singularLocus(P4/X');
dim singX'

-- experiment 1 completed, the answer suggested is yes.
L=ideal random(P15^1,P15^{2:-1})
dim (Y+L)
pts=decompose(Y+L);
netList apply(pts,c->(dim c, degree c))
p=first pts
elapsedTime betti(sp4=saturate(p^4+Y))
--betti(H1=ideal(gens sp4*random(source gens sp4,P15^{-1}))
h5=(gens sp4)_{0..5}
P5=kk[z_0..z_5]
elapsedTime betti(Z=trim ker map(P15/Y,P5,h5))
minimalBetti Z
betti(fZ=res Z)
singPtZ=prune (ker transpose fZ.dd_5/image transpose fZ.dd_4)
h4=presentation singPtZ
minimalBetti(X'=trim ker map(P5/Z,P4,h4))
singX'=ideal singularLocus(P4/X');
dim singX'
-- with high probability any point on X can be the 4-fold point.
-- The other two points are preimage of the singular point of
-- the projection to P5.
-- => Picard rank of Y=Xmin should be 2!


elapsedTime H1'=trim ker map(P4/H1,P15, h6b|h6a);
dim H1', degree H1', genus H1'
betti H1'
elapsedTime betti(E3'=trim  ker map(P4/E3,P15, h6b|h6a))
dim E3', degree E3', genus E3', betti Y
elapsedTime betti(H2a'=trim  ker map(P4/H2a,P15, h6b|h6a)) -- 115.006s elapsed
dim H2a',degree H2a', genus H2a',betti Y
elapsedTime betti(ZX'=trim  ker map(P4/(Z+X),P15, h6b|h6a)) -- 1015.09s elapsed
dim ZX',degree ZX', genus ZX',betti Y
-- all 4 curves tested are linearly equivalent to a multiple of the hyperplane class


P12=kk[y_0..y_12]
Y0=sub(Y,P12); dim Y0, degree Y0
elapsedTime minimalBetti(Y0,DegreeLimit=>3,LengthLimit=>7)  -- 46.8379s elapsed
-*
-- Get the following betti numbers in examples over three differnet 4 digits 
-- primes:
             0  1   2    3    4    5    6    7
o56 = total: 1 78 560 2002 4368 6006 5801 5801
          0: 1  .   .    .    .    .    .    .
          1: . 78 560 2002 4368 6006 4576 1225
          2: .  .   .    .    .    . 1225 4576
betti tateresolustionOfSurface X
-- => Y is not general
-- => map M->Fg is not dominant with high probability

1225/7==175. We expect counted with multiplicity perhaps 175 g^1_8 or infinitly many g^1_8

g=5,d=3,g=15,d=3+5
g^2_10, 
binomial(10-1,2)-15
*-
------ to be continued


-- case (11, 11, 5, 2, 15) -- most likely not dominant
restart
needsPackage"NongeneralTypeSurfacesInP4"
kk=ZZ/nextPrime 10^4;P4=kk[x_0..x_4];
setRandomSeed("fix very good decomposition of D");
--viewHelp "NongeneralTypeSurfacesInP4"

minimalBetti(X=K3surfaceD11S11Ln(P4,3))
(d,sg) =(degree X, sectionalGenus X)
HdotK(d,sg)==9
Ksquare(d,sg,2)==-5
R5=residualInQuintics X; dim R5, degree R5, degree (R5+X)
LeBarzN6(d,sg,2)==4
pd={1,2,2,2,2}

elapsedTime betti (D=canonicalDivisor X)  -- 2931.75s elapsed
elapsedTime selfIntersectionNumber(X,D)
elapsedTime netList apply(cD=decompose D,c->(dim c, degree c, genus c))

betti saturate cD_2






polarizationDegree=d+sum(pd,k->k^2)
polGenus=sub((polarizationDegree+2)/2,ZZ)
netList apply(cD,c->(dim c, degree c, genus c))
elapsedTime sD2s=apply(toList(1..3),i->saturate((cD_i)^2+X));
elapsedTime sD2s=apply(toList(1..2),i->saturate((cD_i)^2+X));
betti(D1=intersect(sD2s|{cD_0}))
betti(H5=ideal(gens D1*random(source gens D1,P4^{-5})))
elapsedTime betti(residual=(X+H5):D1)
degree residual
betti (res1=trim ideal((gens residual)%X))
betti (H6=trim ideal( (gens intersect((ideal vars P4)^6,res1))%X))
betti(h6a=gens trim ideal (((gens H6))%(X+H5)))
betti (h6b=map(P4^1,,vars P4*H5_0))
P15=kk[y_0..y_15]
elapsedTime betti(Y=trim ker map(P4/X,P15, h6b|h6a))  -- 272.168s elapsed

elapsedTime (dim Y, degree Y, genera Y)

--elapsedTime betti(fY=res(Y,LengthLimit=>2,DegreeLimit=>2)) 

L4=ideal(y_0..y_4)
betti(pts1=saturate (L4+Y))
degree pts1, dim pts1
elapsedTime pts=apply(cD,c->(elapsedTime p=trim ker map(P4/c,P15, h6b|h6a);
	<< betti p <<endl;p));
netList apply(pts_{0..2}, p-> transpose syz transpose sub(jacobian p,kk))	
tally apply(cpts1=decompose pts1,c->betti c)
betti(e2=intersect(apply(cpts1,c->saturate(c^2+Y))))
betti(e3=ideal (gens e2)_{0..2})
betti(eq3=intersect(e3,Y))
betti(feq3=res(eq3,LengthLimit=>2,DegreeLimit=>3))
betti (q2=(gens eq3)_{0,1})
P1=kk[s_0,s_1]
P15xP1=P15**P1
q2g=sub(q2,P15xP1)*transpose sub(vars P1,P15xP1)
betti(hess =diff(transpose sub(vars P15,P15xP1), diff(sub(vars P15,P15xP1),q2g)))
betti(J=trim minors(3,map(P1^16,,sub(hess,P1))))
dim J
ring Y

L4=ideal( (vars P15)_{0..4})
betti(eq=intersect(L4,Y))
betti(eqg=(gens eq)_{0..24})
P1=kk[t_0..t_24]
P15xP1=P15**P1
betti(q2g=sub(eqg,P15xP1)*transpose sub(vars P1,P15xP1))
betti(hess =diff(transpose sub(vars P15,P15xP1), diff(sub(vars P15,P15xP1),q2g)))
elapsedTime betti(J=trim minors(5,map(P1^16,,sub(hess,P1))))





B0plusA=intersect cpts1
betti B0plusA
betti(qs=(gens B0plusA)_{11..20})
P4y=kk[support qs];dim P4y==5
betti(qs1=ideal sub(qs,P4y))
minimalBetti qs1
betti(fqs1=res qs1)
fqs1.dd_4
-*
P3=kk[w_0..w_3]
P4xP3=P4y**P3
betti transpose (sub(fqs1.dd_4,P4xP3)*transpose sub(vars P3,P4xP3))
betti(m5x15=diff(transpose sub(vars P4y,P4xP3),transpose (sub(fqs1.dd_4,P4xP3)*transpose sub(vars P3,P4xP3))))
betti (m5x15P3=map(P3^5,,sub(m5x15,P3)))
R=ann coker m5x15P3
minimalBetti R
dim R, degree R
elapsedTime (cR=decompose R)
netList apply(cR,c->(dim c, degree c, betti c))
I1=trim ideal(fqs1.dd_4*sub(syz transpose jacobian first cR,kk))
syz transpose jacobian I1
*-
dim qs1,degree qs1
cqs1=decompose qs1;#cqs1
netList apply(cqs1,c->(dim c, degree c , betti c))
betti (a=intersect(cqs1_{0,2}))
betti (b=intersect(cqs1_{1,2}))
betti(A=ideal (gens trim(sub(ideal(a_0),P15)+B0plusA))_{0..11})
betti(B=ideal (gens trim(sub(ideal(b_0),P15)+B0plusA))_{0..11})
dim A, dim B
dim (A+Y),degree (A+Y)
betti intersect(B,L4)





P9=kk[z_0..z_9]
P15xP9=P15**P9
betti(qg=sub(qs,P15xP9)*sub(transpose vars P9,P15xP9))
v5=sub(gens ideal support qs,P15xP9)
betti(hess=map(P9^5,,sub(diff(transpose v5,diff(v5,qg)),P9)))
betti(I3=saturate minors(3,hess))
dim I3
minimalBetti I3
betti(I2=saturate minors(2,hess))
I2
elapsedTime cI3=decompose I3;#cI3











P12=kk[y_1..y_11,y_13..y_14]
dim P12==13
Y0=sub(Y,P12); dim Y0, degree Y0
elapsedTime minimalBetti(Y0,DegreeLimit=>3,LengthLimit=>7)  -- 49.1828s elapsed
-*
-- Get the following betti numbers in examples over three differnet 4 digits 
-- primes:
             0  1   2    3    4    5    6    7
o60 = total: 1 78 560 2002 4368 6006 5311 5311
          0: 1  .   .    .    .    .    .    .
          1: . 78 560 2002 4368 6006 4576  735
          2: .  .   .    .    .    .  735 4576
735/7==105
-- => this special X does not give a general K3 of genus 15 by Claire's theorem 
--    on the generic Green's Conjecture.
--    expecte 105 g^1_8's on a curve section (counted with multiplcity)
-- If the curve sections have a model in P3 of degree 12, then the 105 4-secant lines give the desired
-- 105 g^1_8.
-- Any C \subset P3 of genus 15 and degree 12 lies on a unique quartic:
-- h^0(O_C(2))=2*12+1-15=10, assuming h^1(O_C(2))=0, (unless O_C(2)=omegaC(-4pts) since 28-2*12=4 )
-- => h^0(O_C(4))=10+2*12=34, h^0(O_P3(4))=binomial(3+4,3)=35.
*-

-- Get a K3 with intersection matrix
M=matrix{{4,12},{12,28}}   
det M==-32
N=matrix{{1,-1},{0,1}}
transpose N*M*N==matrix {{4, 8}, {8, 8}}
-- => a genus 5 curve of degree 8
 8+1-5==4
-- which is non special
{1,4,12,20,28,36,44}-apply(7,i->binomial(i+3,3))
matrix{{1,0,0},{0,0,0},{2,8,5}}

restart
kk=ZZ/nextPrime 10^2
P3=kk[z_0..z_3]
betti (B=(syz (vars P3++vars P3))*random(P3^{12:-1},P3^{5:-1}))
betti (sB=syz transpose B)
minimalBetti(G=ann coker transpose sB)
betti(K3=ideal (gens G*random(source gens G,P3^{-4})))

betti(B1= (syz (vars P3++vars P3)*random(P3^{12:-2},P3^{6:-2})))
minimalBetti(K3=ann coker transpose B1)



P5=kk[u_0..u_5]
P3xP5=P3**P5
graph=sub(vars P5,P3xP5)*sub(transpose B1,P3xP5)
graph1=ideal graph+sub(K3,P3xP5)
betti(graph2=saturate(graph1,ideal sub(vars P3,P3xP5)))
betti(Z=trim sub(graph2,P5))
dim Z, degree Z, minimalBetti Z
L=prune coker sub(diff(transpose sub(vars P3,P3xP5),gens graph2),P5)
ann L == Z
minimalBetti L
P15=kk[y_0..y_15]
betti (m16=prune truncate(-1,coker transpose B1))
PK3=P3/K3
betti (sm16t=syz sub(transpose presentation m16,PK3))
betti syz sm16t
trim sub(ideal sm16t,P3)
binomial(5+3,3)
sm16t
P3w=kk[w_0..w_3]
P3xP3=P3w**P3
betti(m2x4=map(P3xP3^2,,sub(vars P3w,P3xP3)||sub(vars P3,P3xP3)))

K3xK3=sub(K3,P3xP3)+sub(sub(K3,vars P3w),P3xP3)
mP3xP3a=sub(ideal vars P3,P3xP3)
mP3xP3b=sub(ideal vars P3w,P3xP3)
betti(diag=saturate(saturate(minors(2,m2x4)+K3xK3,mP3xP3a),mP3xP3b))
betti(fdiag=res diag)
apply(6,i->tally degrees fdiag_i)


degrees source gens diag
map(P3xP3^1,,matrix {apply(5,i->diag_(5+i))})

P3xP15=P3**P15
betti(gra=ideal (sub(vars P15,P3xP15)*sub(presentation m16,P3xP15)))
gra1=gra+sub(K3,P3xP15);
elapsedTime betti(gra2=saturate(gra1,ideal sub(vars P3,P3xP15))) -- 13.5612s elapsed
betti(Y=trim sub(gra2,P15))
betti(L'=prune coker sub(diff(transpose sub(vars P3,P3xP15),gens gra2),P15))
ann L' == Y
-*
elapsedTime betti(fY=res(Y,Strategy=>Nonminimal,LengthLimit=>7))  -- 300.018s elapsed

pos=positions( degrees fY_7,d->d=={8});#pos
pos1=positions(degrees fY_6,d->d=={8});#pos1
betti(constantPart=fY.dd_7^pos1_pos)
elapsedTime betti(sconst=syz constantPart) -- takes too long
*-


-- number of such K3's
3*5-3+6==18
restart
kk=ZZ/nextPrime 10^4;P2=kk[w_0..w_2]
E=homogenize(ideal(w_2^2-w_1^3+random(kk)*w_1+random(kk)),w_0)
p=ideal(w_0,w_1)
betti(eightP=saturate(p^8+E))
H4=ideal(gens eightP*random(source gens eightP,P2^{-4}))
betti(residual=(E+H4):eightP)
degree residual==degree H4*degree E - degree eightP
betti (h8=gens trim ideal(gens truncate(4,residual)%E))
P7=kk[u_0..u_7]
betti(E8=trim ideal ker map(P2/E,P7,h8))
fourPairsOfPoints=apply(4,i->apply(2,j->(
	    while ( threePoints=decompose(E+ideal random(1,P2));
		degree first threePoints >1) do ();
	    first threePoints)))
fourInP7=apply(fourPairsOfPoints,c->(midPt=sum(c,q->
	    syz transpose jacobian ker map(P2/q,P7,h8));
	ideal(vars P7*syz transpose midPt)))
betti(h4=(gens intersect(fourInP7))_{0..3})
P3=kk[z_0..z_3]
minimalBetti(G=ker map(P7/E8,P3,h4))	
degree G, genus G
singG=radical saturate ideal singularLocus(P3/G)
decompose singG
Z=ideal(gens G*random(source gens G,P3^{-4}))
assert(dim ideal jacobian Z==0)
betti(C=intersect(Z+ideal random(1,P3),G))
betti(H5=ideal(gens C*random(source gens C,P3^{-5})))
betti(res1=(H5+Z):C)
betti(doublePoints=saturate(singG^2+Z))
dim doublePoints, degree doublePoints
betti(res2=intersect(res1,doublePoints))
betti(H5'=ideal(gens res1*random(source gens res1 ,P3^{-5})))
betti(C'=(H5'+Z):res1)
degree C', genus C'
dim singularLocus(P3/C')
betti(H5''=ideal(gens C'*random(source gens C' ,P3^{-5})))
betti(res2=(H5''+Z):C')
betti(res3=intersect(res2,doublePoints))
betti(H5s=ideal(gens res3*random(source gens res3 ,P3^{-5})))
betti(Cs=(H5s+Z):res2)
tally apply(decompose saturate ideal singularLocus(P3/Cs),c->(dim c, degree c, betti c))
tally apply(decompose Cs,c->(dim c, degree c))
--=> all double linked curves with the four double points at the singlar points of G
--   are reducible.
--=> my naive guess, that the 4 special nodes coincide with the singularies
--   of the geometric genus 1  curve G, is wrong.

------ to be continued

-- case (11, 11, 5, 2, 16)
restart
needsPackage"NongeneralTypeSurfacesInP4"
kk=ZZ/nextPrime 10^5;P4=kk[x_0..x_4];E=kk[e_0..e_4,SkewCommutative=>true];
setRandomSeed("fix very good decomposition of D");
--viewHelp "NongeneralTypeSurfacesInP4"

minimalBetti(X=K3surfaceD11S11Ln(P4,2))
(d,sg) =(degree X, sectionalGenus X)
HdotK(d,sg)==9
Ksquare(d,sg,2)==-5
R5=residualInQuintics X; dim R5, degree R5, degree (R5+X)
LeBarzN6(d,sg,2)==4
pd={1,1,2,2,3}

polarizationDegree=d+sum(pd,k->k^2)
polGenus=sub((polarizationDegree+2)/2,ZZ)

elapsedTime betti (D=canonicalDivisor X) -- 4050.15s elapsed 
elapsedTime selfIntersectionNumber(X,D)
elapsedTime tally apply(cD=decompose D,c->(dim c, degree c, genus c))

netList apply(cD,c->(dim c, degree c, genus c))
elapsedTime sD3=saturate((cD_3)^2+X);
betti(sD0=saturate((cD_0)^3+X));
betti(D1=intersect(sD0,sD3,cD_1,cD_2))
betti(H5=ideal(gens D1*random(source gens D1,P4^{-5})))
betti(residual=(X+H5):D1)
degree residual
betti (res1=trim ideal((gens residual)%X))
betti (H6=trim ideal( (gens intersect((ideal vars P4)^6,res1))%X))
betti(h6a=gens trim ideal (((gens H6))%(X+H5)))
betti (h6b=map(P4^1,,vars P4*H5_0))
P16=kk[y_0..y_16]
elapsedTime betti(Y=trim ker map(P4/X,P16, h6b|h6a))  

dim Y, degree Y, genera Y
L4=ideal(y_0..y_4)
betti(pts1=saturate (L4+Y))
degree pts1, dim pts1
elapsedTime pts=apply(cD,c->(elapsedTime p=trim ker map(P4/c,P16, h6b|h6a);
	<< betti p <<endl;p));
netList apply(pts_{0..2}, p-> transpose syz transpose sub(jacobian p,kk))	
tally apply(cpts1=decompose pts1,c->betti c)

P13=kk[y_0..y_13]
dim P13==14
Y0=sub(Y,P13); dim Y0, degree Y0
elapsedTime minimalBetti(Y0,DegreeLimit=>3,LengthLimit=>7)  -- 197.412s elapsed

-*
             0  1   2    3    4     5     6     7
o49 = total: 1 91 715 2835 7007 11375 11583 10010
          0: 1  .   .    .    .     .     .     .
          1: . 91 715 2835 7007 11375 11583  5005
          2: .  .   .    .    .     .     .  5005


-- => could be a general K3 of genus 16
*-

-- case (11, 11, 5, 2, 18)
restart
needsPackage"NongeneralTypeSurfacesInP4"
kk=ZZ/nextPrime 10^4;P4=kk[x_0..x_4];E=kk[e_0..e_4,SkewCommutative=>true];
setRandomSeed("fix very good decomposition of D");
--viewHelp "NongeneralTypeSurfacesInP4"

minimalBetti(X=K3surfaceD11S11Ln(P4,1))
(d,sg) =(degree X, sectionalGenus X)
HdotK(d,sg)==9
Ksquare(d,sg,2)==-5
R5=residualInQuintics X; dim R5, degree R5, degree (R5+X)
LeBarzN6(d,sg,2)==4
pd={1,1,1,2,4}

polarizationDegree=d+sum(pd,k->k^2)
polGenus=sub((polarizationDegree+2)/2,ZZ)

elapsedTime betti (D=canonicalDivisor X) -- 8.24154s elapsed
elapsedTime selfIntersectionNumber(X,D)
elapsedTime tally apply(cD=decompose D,c->(dim c, degree c, genus c))

netList apply(cD,c->(dim c, degree c, genus c))
elapsedTime sD1=saturate((cD_1)^4+X);
betti(sD0=saturate((cD_0)^2+X));
betti(D1=intersect(sD0,sD1,cD_2))
minimalBetti X
betti(H6=ideal(gens D1*random(source gens D1,P4^{-6})))
betti(residual=(X+H6):D1)
degree residual
betti (res1=trim ideal((gens residual)%X))
betti (H7=trim ideal( (gens intersect((ideal vars P4)^7,res1))%X))
betti(h7a=gens trim ideal (((gens H7))%(X+H6)))
betti (h7b=map(P4^1,,vars P4*H6_0))
P18=kk[y_0..y_18]
elapsedTime betti(Y=trim ker map(P4/X,P18, h7b|h7a))  -- 1407.86s elapsed 

dim Y, degree Y, genera Y
L4=ideal(y_0..y_4)
betti(pts1=saturate (L4+Y))
degree pts1, dim pts1
elapsedTime pts=apply(cD,c->(elapsedTime p=trim ker map(P4/c,P18, h7b|h7a);
	<< betti p <<endl;p));
netList apply(pts_{0,1}, p-> transpose syz transpose sub(jacobian p,kk))	
tally apply(cpts1=decompose pts1,c->betti c)

P15=kk[y_0..y_15]
dim P15==16
Y0=sub(Y,P15); dim Y0, degree Y0
elapsedTime minimalBetti(Y0,DegreeLimit=>3,LengthLimit=>8)  
-*

*-

restart
-- computations for the (11, 11, 5, 2, 21) example:
needsPackage"NongeneralTypeSurfacesInP4"
kk=ZZ/nextPrime 10^4;P4=kk[x_0..x_4];E=kk[e_0..e_4,SkewCommutative=>true];
setRandomSeed("fix decomposition of D");

minimalBetti(X=K3surfaceD11S11Ln(P4,0))

D=canonicalDivisor X;
selfIntersectionNumber(X,D)
elapsedTime tally apply(cD=decompose D,c->(dim c, degree c, genus c))
(d,sg) =(degree X, sectionalGenus X)
HdotK(d,sg)==9
Ksquare(d,sg,2)==-5
R5=residualInQuintics X; degree R5, dim R5
--tally apply(primaryDecomposition(R5+X),c-> (dim c, degree c, genus c))
LeBarzN6(d,sg,2)==4
pd={1,1,1,1,5}
polarizationDegree=d+sum(pd,k->k^2)
polGenus=sub((polarizationDegree+2)/2,ZZ)
elapsedTime D=canonicalDivisor X;
betti D

netList apply(cD,c->(dim c, degree c, genus c))


betti(sD3=saturate(X+cD_3^5))
degree sD3
betti (D1=intersect(sD3,cD_0,cD_1,cD_2))
matrix apply(cD,c->apply(cD,d-> dim(c+d)))
betti(H7=ideal(gens D1*random(source gens D1,P4^{-7})))
elapsedTime betti(residual=(X+H7):D1) -- 14.4742s elapsed
degree residual
betti (res1=trim ideal((gens residual)%X))
betti (H8=trim ideal( (gens intersect((ideal vars P4)^8,res1))%X))
betti(h8a=gens trim ideal (((gens H8)_{0..21})%(X+H7)))
betti (h8b=map(P4^1,,vars P4*H7_0))
P21=kk[y_0..y_21]
elapsedTime betti(Y=trim ker map(P4/X,P21, h8b|h8a)) -- 4880.71s elapsed

g=21
h={1,g-2,g-2,1}
apply(23,i->sum(4,j->(-1)^(2*i-j-1)*h_j*binomial(19,i-j)))
i=11
m=sum(2,j->(-1)^(2*i-j-1)*h_j*binomial(19,i-j))
m==1679600
-- expect a g^1_11
dim Y, degree Y, genera Y

L4=ideal(y_0..y_4)
betti(pts1=saturate (L4+Y))
degree pts1, dim pts1
elapsedTime pts=apply(cD,c->(elapsedTime p=trim ker map(P4/c,P21, h8b|h8a);
	<< betti p <<endl;p));
netList apply(pts_{0,1,3}, p-> transpose syz transpose sub(jacobian p,kk)	)
pts_2
elapsedTime betti (p3=saturate((pts_3)^5+Y))
elapsedTime betti(pts1a=(pts1:pts_2))
elapsedTime betti(pts1b=((pts1a:pts_1):pts_0))
degree pts1, degree pts1a, degree pts1b

A2=kk[w,z]
betti(m5=(ideal vars A2)^5)
m5a=ideal(gens m5*random(source gens m5,A2^{5:-5}));
degree m5a, degree m5

P18=kk[y_0..y_18]
Y0=sub(Y,P18);dim Y0, degree Y0

betti(b2=sub(basis(2,P18/Y0),P18))
betti(m19x19=(transpose b2*vars P18)%Y0)
betti(b3=sub(basis(3,P18/Y0),P18))
b3
m19x19a=sub(contract(b3,m19x19),kk)
betti(b2a=sub(inverse(m19x19a),P18)*map(P18^{19:0},,transpose b2))
b2a
m19x19b=contract(b3,(b2a*vars P18)%Y0)
betti (K10=koszul(10,vars P18))
elapsedTime betti(K10a=(K10**vars P18)%Y0)

elapsedTime betti(K10b=contract(transpose b2,K10a))

elapsedTime betti( M=map(kk^1755182,,sub(K10b,kk)))


elapsedTime minimalBetti(Y0,DegreeLimit=>3,LengthLimit=>10)
-*
 "X='doneLL'",PARA{},
	"Y='doneData.dbm'",PARA{},
	"openOutAppend X",PARA{},
	    "X << ',' ",PARA{},
        "X<<close;",PARA{},
	"doneLL=getFromDisk X;#doneLL",PARA{},
	"Y=openDatabase Xdbm",PARA{},
	"#keys Y",PARA{},
	"keys Y",PARA{},
	"listOfIdeals=apply(doneLL,L->(R=value Y#(toString L|'ring');
	        I=value (Y#(toString L|ideal))));",PARA{},
        "close Y",PARA{},
*-
-------- to be continued ---------
