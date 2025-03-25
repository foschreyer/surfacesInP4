

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




