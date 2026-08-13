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

LeBarzN6(d,sg,2)==4
pd={1,1,1,1,5}
polarizationDegree=d+sum(pd,k->k^2)
polGenus=sub((polarizationDegree+2)/2,ZZ)
elapsedTime D=canonicalDivisor X;


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
g=21
h={1,g-2,g-2,1}
apply(23,i->sum(4,j->(-1)^(2*i-j-1)*h_j*binomial(19,i-j)))
i=11
m=sum(2,j->(-1)^(2*i-j-1)*h_j*binomial(19,i-j))
m==1679600
apply(4,j->h_j*binomial(19,i-j))
-- expect a g^1_11's


elapsedTime betti(Y=trim ker map(P4/X,P21, h8b|h8a)) -- 4880.71s elapsed


elapsedTime (dim Y, degree Y, genera Y)

L4=ideal(y_0..y_4)
elapsedTime X'=trim ker map(P21/Y,P4,gens L4);
assert(
    X==X'
    )

-* computing betti numbers using the artinian reduction *-
P18=kk[y_0..y_18]
Y0=sub(Y,P18);dim Y0, degree Y0
assert(dim Y0==0)
-* two much memory on my machine
elapsedTime minimalBetti(Y0,DegreeLimit=>3,LengthLimit=>10)
*-

betti(b2=sub(basis(2,P18/Y0),P18))
betti(m19x19=(transpose b2*vars P18)%Y0)
betti(b3=sub(basis(3,P18/Y0),P18))
b3
m19x19a=sub(contract(b3,m19x19),kk)
betti(b2a=sub(inverse(m19x19a),P18)*map(P18^{19:0},,transpose b2))
-- b2a is the dual basis to y_0..y_18
m19x19b=contract(b3,(b2a*vars P18)%Y0)

-* computing the middle Koszul matrix of the complex with betti numbers
 {75582, 1755182, 1755182, 75582} *-

betti (K10=koszul(10,vars P18))

elapsedTime betti(K10a=map(P18^92378,,(K10**vars P18)%Y0)) -- 497.972s elapsed
-*
elapsedTime betti (sK10a=syz(K10a,DegreeLimit=>1))
-- maybe DegreeLimit=>2 is the correct choice

numberOfExtraSyzygies=rank source sK10a-75582
*-



elapsedTime betti(K10b=contract(transpose b2,K10a))) -- 3187.18s elapsed
char kk==10007

-- the big KoszulMatrix
elapsedTime betti( M=map(kk^1755182,,sub(K10b,kk))) -- 319.991s elapsed

-*
elapsedTime betti (sM=syz M)
numberOfExtraSyzygies=rank source sM-75582
*-

-* how to comunicate with a .dbm file
	Xdbm="koszulMatrix.dbm";
        Y=openDatabase Xdbm";
	Y#("MM")=M;
        close Y;
*-

-* the following needed too much memory on my machine and produced too much heat *-
elapsedTime sparseMatrix = flatten for i from 0 to 1755182-1 list (
    for j from 0 to 1755182-1 list (
	if M_(i,j) != 0 then (i,j,M_(i,j)) else continue)); --

#sparseMatrix, 10*1755182, 19*10*1755182
  
