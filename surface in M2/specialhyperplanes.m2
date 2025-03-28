

--ring P4


cs=curve+surf;
decompose cs  --the intersection points of 2x4 curve and 2x3 surface

X1=X+ideal(x_0+x_1+x_2+x_3+x_4);  --special hyperplane dual to a point in cs
X1=saturate X1;
betti X1--on a quartic

toString decompose X1  --is X1 reducible?

f4=submatrix(gens X1,{0,1});
f5=(random(P4^1,P4^4))*transpose (submatrix(gens X1,{2,3,4,5}));
f45=ideal flatten f4+ideal flatten f5;-- a complete intersection 1,4,5 that contain X1
X8=f45:X1;
X8=saturate X8;
betti X8
degree X8,dim X8

f3=submatrix(gens X8,{0,1,2});
f34=ideal flatten f3;--a complete intersection 1,3,4 containing X8
betti f34
f34=ideal mingens f34;
degree f34,dim f34
X4=f34:X8;
X4=saturate X4;
betti X4
degree X4, dim X4, genus X4-- four lines?

XX4=X+X11;
XX4=ideal mingens XX4;
degree XX4, dim XX4

sngX=dim(X+minors(2,jacobian X))
sngX1=dim(X1+minors(3,jacobian X1))

decompose X1

--analysis of "AboSurface" N=113,114 including code to compute 
-- residual in quintics (6-secant lines and 11-secant conics)
-- intersection of (2x3) surface and (2x4) curve
-- intersection of veronese surface of columns in (2x3) and veronese P3 of columns in (2x4)

elapsedTime X=AboSurface(114,4);
singX=(X+minors(2,jacobian X));
dim(singX)

--adjuction
elapsedTime (numList,L1,L2,J)=adjunctionProcess(X,4);
numList

--residual in quintics
X5=ideal(gens X)_{0..4};
dim X5, degree X5, genera X, genera X5
R=X5:X
RX=R+X;
dim R, degree R, degree RX, minimalBetti R

--inteserction of curve and surface (0,1,2 points ?)

P4=ZZ/11[v_0..v_4]
m3x2'=sub(m2x3,vars P4)
m2x4'=sub(m4x2,vars P4)
surf=minors(2,m3x2');
curve=minors(2,m2x4');
dim(curve+surf),dim curve, dim surf
degree(curve+surf)


--The intersection of the row surface of m3x2 and the  column threefold of m2x4 in G(2,5) (6 points when N=114, 7 when N=113)

S=E[a1,a2,a3,a4]
ee1=matrix {{e_0,e_1,e_2,e_3,e_4}}
ee=ideal (e_0,e_1,e_2,e_3,e_4)
ee2=ideal mingens ee^2
ef2=sub(ee2,S)

xx3=matrix {{a1,a2,a3}}
xx4=matrix {{a1,a2,a3,a4}}

ex3=sub(m2x3,S)
ex4=sub(m4x2,S)

 yy3=xx3*transpose ex3;
 yy4=xx4*ex4;
y23=submatrix(yy3,{0})*submatrix(yy3,{1});
y23=ideal flatten y23;

y24=submatrix( yy4,{0})*submatrix( yy4,{1});
y24=ideal flatten y24;

yy23=diff(gens ef2,gens y23)
yy24=diff(gens ef2,gens y24)


RT=ZZ/11[y_0,y_1,y_2,y_3,y_4,y_5,y_6,y_7,y_8,y_9]

RTT=ZZ/11[a1,a2,a3,a4]
ay3=sub(yy23,RTT)
ay4=sub(yy24,RTT)
my3=map(RTT,RT,ay3)
my4=map(RTT,RT,ay4)

gy3=kernel my3;
gy4=kernel my4;
degree gy3,dim gy3
degree gy4,dim gy4
gg34=gy3+gy4;
degree gg34,dim gg34
betti gg34
gg34=ideal mingens gg34;
sg34=saturate gg34;
betti sg34


sg5=gy4+ideal(gens gg34)_{0..3};
degree sg5,dim sg5-- the intersection of the veronese threefold with the span of the veronese surface 

toString decompose sg34



