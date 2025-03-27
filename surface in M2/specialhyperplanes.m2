

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




--The intersection of the row surface of m3x2 and the  column threefold of m2x4 in G(2,5)

S=E[a1,a2,a3,a4]
ee1=matrix {{e_0,e_1,e_2,e_3,e_4}}
ee=ideal (e_0,e_1,e_2,e_3,e_4)
ee2=ideal mingens ee^2
ef2=sub(ee2,S)

xx3=matrix {{a1,a2,a3}}
xx4=matrix {{a1,a2,a3,a4}}

ex3=sub(m3x2,S)
ex4=sub(m2x4,S)

 yy3=xx3*ex3;
 yy4=ex4*transpose xx4;
y23=submatrix(yy3,{0})*submatrix(yy3,{1});
y23=ideal flatten y23;

y24=submatrix(transpose yy4,{0})*submatrix(transpose yy4,{1});
y24=ideal flatten y24;

yy23=diff(gens ef2,gens y23)
yy24=diff(gens ef2,gens y24)

ST=ZZ/3[y_0,y_1,y_2,y_3,y_4,y_5,y_6,y_7,y_8,y_9,a1,a2,a3,a4]
sy3=sub(yy23,ST)
sy4=sub(yy24,ST)



y23=(-e_2*a1+(-3*e_1+3*e_4)*a2+(-e_1+2*e_4)*a3)*((e_1+e_2)*a1+(3*e_0+3*e_1-3*e_3-3*e_4)*a2+(e_0+e_1-2*e_3-2*e_4)*a3)
y24=((-e_0-2*e_2-3*e_4)*a1+(-3*e_0+2*e_1+3*e_2-2*e_3+3*e_4)*a2+(2*e_0-2*e_2+e_3+2*e_4)*a3+(-2*e_0+3*e_1+2*e_2-2*e_3)*a4)*((-e_2+2*e_3+3*e_4)*a1+(-e_2-e_3)*a2+(e_1+2*e_2-3*e_3)*a3+(e_0+e_3+3*e_4)*a4)


y23=((e_2+e_4)*a1+(-e_1-3*e_2+2*e_4)*a2+(-3*e_1+3*e_2+3*e_4)*a3)*((2*e_1-3*e_2+2*e_3-3*e_4)*a1+(-2*e_0-3*e_1+2*e_2-3*e_3+e_4)*a2+(e_0+e_1-2*e_2-e_3-2*e_4)*a3)
y24=((2*e_0-e_1-2*e_2-2*e_3-3*e_4)*a1+(-3*e_0+2*e_1+3*e_2-e_3)*a2+(e_0-2*e_1-e_2+3*e_3-e_4)*a3+(-3*e_0+e_1+2*e_2+3*e_3-3*e_4)*a4)*((-e_2+e_3+e_4)*a1+(e_1+2*e_2-3*e_3)*a2+(-2*e_2-2*e_3)*a3+(e_0+3*e_2+e_3-2*e_4)*a4)

toString p23
toString y24
	
ST=ZZ/3[y_0,y_1,y_2,y_3,y_4,y_5,y_6,y_7,y_8,y_9,a1,a2,a3,a4]
sy3=sub(yy23,ST)
sy4=sub(yy24,ST)


gz3=matrix{{y_0,y_1,y_2,y_3,y_4,y_5,y_6,y_7,y_8,y_9}}+sy3;
gz4=matrix{{y_0,y_1,y_2,y_3,y_4,y_5,y_6,y_7,y_8,y_9}}+sy4;
hz3=ideal flatten gz3;
hz4=ideal flatten gz4;
ez3=eliminate(hz3,{a1,a2,a3,a4});
ez4=eliminate(hz4,{a1,a2,a3,a4});
ez3=ideal mingens ez3;--a veronese surface  
ez4=ideal mingens ez4;--a veronese P3
degree ez3,dim ez3
degree ez4,dim ez4
pz=ez3+ez4;
pz=ideal mingens pz;
degree pz,dim pz  -- the 120-N?







---  X11,X12 components of X1, when reducible  
X11=ideal(x_0+x_1+x_2,x_1^2+x_2^2-x_3^2-x_3*x_4+x_4^2,x_1*x_2*x_3^2-x_1*x_3^3-x_2*x_3^3+x_1*x_2*x_3*x_4+x_2^2*x_3*x_4-x_1*x_3^2*x_4+x_2*x_3^2*x_4+x_3^3*x_4
        -x_2^2*x_4^2+x_1*x_3*x_4^2+x_2*x_4^3+x_3*x_4^3+x_4^4,x_2^3*x_3-x_2^2*x_3^2+x_1*x_3^3+x_3^4+x_1*x_2^2*x_4-x_2^3*x_4+x_2^2*x_3*x_4-x_2*x_3^2*x_4-x_3^3*x_4
        -x_1*x_2*x_4^2-x_2^2*x_4^2+x_1*x_3*x_4^2+x_3^2*x_4^2-x_1*x_4^3-x_4^4,x_1*x_2^2*x_3-x_2^2*x_3^2-x_1*x_3^3-x_2*x_3^3-x_1*x_2^2*x_4-x_2^3*x_4-x_1*x_3^2*x_4
        +x_2*x_3^2*x_4-x_3^3*x_4+x_1*x_2*x_4^2+x_3^2*x_4^2+x_1*x_4^3-x_2*x_4^3+x_4^4,x_2^4-x_2^2*x_3^2-x_1*x_3^3-x_2*x_3^3+x_3^4-x_1*x_2^2*x_4-x_2^3*x_4+x_2*x_3
        ^2*x_4+x_1*x_2*x_4^2-x_1*x_3*x_4^2+x_3^2*x_4^2+x_1*x_4^3-x_2*x_4^3+x_3*x_4^3-x_4^4,x_1*x_2^3+x_2^2*x_3^2-x_2*x_3^3+x_3^4-x_1*x_2^2*x_4+x_2^3*x_4-x_1*x_3
        ^2*x_4-x_2*x_3^2*x_4+x_3^3*x_4-x_1*x_2*x_4^2-x_3^2*x_4^2+x_2*x_4^3+x_3*x_4^3-x_4^4);
    X12=ideal(x_0+x_1+x_2,x_1^2+x_1*x_2-x_2^2-x_1*x_3-x_2*x_3-x_3^2-x_1*x_4-x_2*x_4-x_3*x_4+x_4^2,x_2^4+x_1*x_2^2*x_3+x_2^3*x_3+x_1*x_2*x_3^2+x_1*x_3^3-x_2*x_3^
        3+x_3^4-x_1*x_2^2*x_4-x_2^3*x_4+x_1*x_2*x_3*x_4-x_2^2*x_3*x_4+x_1*x_3^2*x_4-x_2*x_3^2*x_4-x_3^3*x_4-x_1*x_2*x_4^2-x_2^2*x_4^2-x_1*x_4^3-x_3*x_4^3-x_4^4
        );




