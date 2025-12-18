-- grassmanian classes
R=ZZ[u_1,u_2,q_1,q_2,q_3,Degrees=>{1,2,1,2,3}]
rel=(1+u_1+u_2)*(1+q_1+q_2+q_3)-1
(mons,coef)=coefficients rel
eqs=ideal apply(toList(1..5),i->(
	pos=positions(degrees source mons,t->t== {i});
	mons_pos*coef^pos))
J=eliminate({q_1,q_2,q_3},eqs)
chow=ZZ[support J, Degrees=>apply(support J,m->degree m)]
J=sub(J,chow)


base=sort sub(basis (chow/J),chow)
(transpose base*base)%J
transpose base|transpose (u_1*base)%J
vP2=(u_1^4-u_2^2)%J
vP2*u_1^2%J
u_1^4%J==vP2+u_2^2

u_1^6%J
transpose base
-- to be continued
