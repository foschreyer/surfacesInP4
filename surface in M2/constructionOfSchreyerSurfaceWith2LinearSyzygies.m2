restart
kk=ZZ/nextPrime 10^3
P4=kk[x_0..x_4]
m2x3=matrix{{x_0,x_1,x_3},{x_1,x_2,x_4}}
scroll=minors(2,m2x3)
hypPlane=ideal x_1
lines1=decompose(hypPlane+scroll)
q2x2= matrix{{x_0,x_2}}||random(P4^1,P4^{2:-1})%hypPlane
quadric=hypPlane+minors(2,q2x2)
Z=intersect(scroll,quadric);minimalBetti Z
twoPointsa=(decompose(quadric+scroll))_{1,2}
if twoPointsa_0+lines1_0==twoPointsa_0 then twoPointsa=twoPointsa_{1,0}
twoPointsb=apply(lines1_{0,1},l->trim(l+lines1_2))
twoLines=apply(2,i->ideal (gens intersect(twoPointsa_i,twoPointsb_i))_{0..2}) 
vertex=ideal random(P4^1,P4^{4:-1})
twoPlanes=apply(twoLines,l->ideal (gens intersect(l,vertex))_{0,1})
while( --get four points defined over kk
    middlePlane=trim sum apply(twoPlanes,p->ideal (gens p*random(source gens p,P4^{-1})));
    betti(conic=ideal (gens saturate( middlePlane+Z))_{0..2});
    betti(threePoints=saturate(middlePlane+scroll));
    twoPoints=apply(2,i->decompose(twoPlanes_i+conic));
not all(twoPoints,a->#a==2)) do ()
twoPoints=apply(twoPoints,a->first a)
apply(2,i->degree(twoPlanes_i+Z)==6)
degree(conic+Z)==5
betti intersect({conic+Z}|twoPoints)
planeCubics=apply(2,i->(p7=saturate intersect(twoPlanes_i+Z,twoPoints_i);
    twoPlanes_i+ideal(gens p7*random(source gens p7,P4^{-3}))));
genus2Curve=intersect(planeCubics|{conic});
dim genus2Curve, degree genus2Curve, genus genus2Curve
betti(p17=saturate(Z+genus2Curve))
degree p17, dim p17 -- 17 point
betti (Z'=intersect(Z,genus2Curve))
ci2=ideal(gens Z'*random(source gens Z',P4^{2:-4}));
Y=ci2:Z; betti Y
unionOfPlanes=intersect(twoPlanes|{middlePlane});minimalBetti unionOfPlanes
betti(Y'=intersect(Y,unionOfPlanes))
ci=ideal(gens Y')_{0,1};
X=ci:Y';
minimalBetti X
(dim X, degree X, (genera X)_1) == (3,11,10)
  

restart
setRandomSeed("ran through smoothly")
kk=ZZ/nextPrime 10^3
T=kk[x_0..x_4]

--m2x3=matrix{{x_0,x_1,x_3},{x_1,x_2,x_4}}
--decompose(minors(2,m2x3)+ideal x_1)

xx=ideal(x_0,x_1,x_2,x_3,x_4)
r3=random(T^2,T^{1:-1})--*transpose gens xx;
h3=matrix{{x_0,x_2},{x_2,x_1}};
hr3=h3||transpose r3;
s3=minors(2,hr3);  --a cubic scroll

h2=matrix{{x_0,x_1}}
r2=random(T^2,T^{1:-1}) --*transpose gens xx;
hr2=h2||transpose r2;
s2=ideal(x_2)+minors(2,hr2);
--s2 is a quadric surface that intersect s3 in its directrix and in two further points  
s23=intersect(s2,s3);minimalBetti s23
s32=saturate(s2+s3);
cs32=primaryDecomposition s32 -- the directrix and 2 points
s321=cs32_0; --the directrix of s3
s322=cs32_1-- one of two isolated points of intersection between s2 and s3
s323=cs32_2-- the other isolated point of intersection between s2 and s3



s3x=s3+ideal(x_2);
cs3x=decompose s3x
--s3x1=ideal(x_2)+ideal(x_2,x_0,x_1)+ideal(x_2,x_1,x_0+14*x_3+6*x_4);--one of two singular points in the hyperplane section of s3 defined by the hyperplane of s2
--s3x2=ideal(x_2)+ideal(x_2,x_0,x_1)+ideal(x_2,x_1-9*x_3+8*x_4,x_0);--the other  singular point in the hyperplane section of s3 defined by the hyperplane of s2
betti(s3x1=trim(cs3x_0+cs3x_1))
betti(s3x2=trim(cs3x_0+cs3x_2))

line=ideal (gens intersect(s322,s3x2))_{0..2}
line+s3==line
if line+s3==line then (s3x1=trim(cs3x_0+cs3x_2);s3x2=trim(cs3x_0+cs3x_1);)
-- ms=ideal flatten (random (T^4,T^5)*transpose gens(ideal(x_0,x_1,x_2,x_3,x_4)));--a choice of vertex for sm, the union of three planes ms12,ms13,ms24, s.t. ms12 meets ms13 and ms24 in a line
ms= ideal random(T^1,T^{4:-1})
betti( s22x=saturate intersect(ms,s322,s3x2))--s323 and s3x2 do not lie in the same line on s3
s32x=saturate intersect(ms,s323,s3x1);--s322 and s3x1 do not lie in the same line on s3
betti s22x  --two linear forms
betti s32x --two linear forms
 
while( -- choose good hyperplanes 
ms1=ideal flatten (random (T^1,T^2)*transpose (gens s32x)_{0..1});
ms2=ideal flatten (random (T^1,T^2)*transpose (gens s22x)_{0..1}); 
ms3=ideal flatten (random (T^1,T^2)*transpose (gens s32x)_{0..1});
ms4=ideal flatten (random (T^1,T^2)*transpose (gens s22x)_{0..1});

ms12=ms1+ms2;
ms13=ms1+ms3;
ms24=ms2+ms4;
sm=saturate intersect(ms12,ms13,ms24);--the union of three planes  ms12,ms13,ms24,
-- s.t. ms12 meets ms13 and ms24 in a line
sms12=saturate(ms12+s23);
--<<degree sms12 <<"proceed if 5 points"<<endl;
sms13=ms13+s23;
--<<degree sms13 <<"proceed if 6 points"<<endl;
sms24=ms24+s23;
--<<degree sms24 <<"proceed if 6 points"<endl;
--betti sms12, betti s23
px12=ideal((gens sms12)_{0..2});-- a conic in the plane ms12
pm123=ms12+ms13+px12;
pm124=ms12+ms24+px12;
cpm123=decompose pm123;
cpm124=decompose pm124;
#cpm123<2 or #cpm124< 2 ) do ()
pm123=first cpm123
pm124=first cpm124
--pm123=ideal(x_3-9*x_4,x_2-x_4,x_1+11*x_4,x_0+13*x_4);  --a choice of point among two in pm123 (it lies on the conic ms12)
--pm124=ideal(x_3-10*x_4,x_2+2*x_4,x_1+10*x_4,x_0-2*x_4);  --a choice of point among two in pm124 (it lies on the conic ms12)

pm12=saturate intersect(sms12,pm123,pm124);
degree pm12, betti pm12  -- proceed if 7 points on the conic ms12
betti(pm13=saturate intersect(sms13,pm123))
degree pm13  -- proceed if 7 points
betti(pm24=saturate intersect(sms24,pm124))
degree pm24  -- proceed if 7 points


--pm133=intersect(pm13, tx3);
--betti pm133--proceed if 28 cubics 
--pm243=intersect(pm24,tx3);
--betti pm243--proceed if 28 cubics
px13=ms13+ideal( gens pm13*random(source gens pm13,T^{-3}))
--px13=ms13+ideal flatten (random(T^1,T^28)*transpose(gens pm133)_{0..27}); -- a cubic in the plane m13
px24=ms24+ideal( gens pm24*random(source gens pm24,T^{-3}))
--px24=ms24+ideal flatten (random(T^1,T^28)*transpose(gens pm243)_{0..27}); -- a cubic in the plane m24
p123=intersect(px12,px13,px24);-- a curve in sm23
assert((degree p123,dim p123, genus p123)==(8,2,2))  --proceed if (8,2,2)
betti(ps123=p123+s23)
degree ps123, dim ps123-- expect 17 points
betti(ts5x=intersect(s23,p123))--the union of the surface s23 and the curve p123
betti(ts5x=saturate ts5x)
betti ts5x-- proceed if 3 quartics and 10 quintics
ts16=ideal flatten (random (T^2,T^3)*transpose((gens ts5x)_{0..2}));
ts11=ts16:s23;-- a surface of degree 11 that contains the curve P123, linked to the surface s23 in two quartics  
betti ts11  --proceed if 2 quartics and 4 quintics
ts11x=intersect(ts11,sm); --a surface of degree 14, the union of ts11 and sm
ts11x=saturate ts11x;
betti ts11x  --proceed if 2 quintics and 10 sextics 
ts25=ideal (gens ts11x)_{0..1}; 
X=ts25:ts11x;  --a surface of degree 11 linked to ts11x
betti res X -- proceed whenever 5 quintics with 2 linear syzgies
degree X,dim X
singX=saturate(X+minors(2,jacobian X));
dim singX, degree singX



X5=ideal(gens X)_{0..4};
R5=X5:X;
R5=saturate R5;
degree R5, dim R5
decompose R5
genera R5
pR5=primaryDecomposition R5;
tally apply(pR5,c->(dim c, degree c, betti c))
matrix apply(pR5,c->apply(pR5,d->dim(c+d)))
Ls=select(pR5,c->dim c== 2)|{planes_0+planes_1,planes_0+planes_2}

apply(Ls,c->degree( radical c +X))
apply(Ls,c->dim(c+ms))
planes=select(pR5,c->dim c==3)
netList (pointsInPlanes=apply(planes,c-> select(primaryDecomposition(c+X),d->dim d==1)))
apply(pointsInPlanes,L->tally apply(L,c->(degree c, degree radical c)))
degree(planes_0+planes_1+X)
netList primaryDecomposition(first planes+X+planes_2)
