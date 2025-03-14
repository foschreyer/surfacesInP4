--(15;5^6,4^2,3^2,2^3,1^2)
--parametricAproach
restart
kk=ZZ/5
P2=kk[t_0..t_2]
P4=kk[x_0..x_4]

findPoints=method()
findPoints(Ring) := P2 -> (count=0;good=0;
    while(
    while (
	  elapsedTime while (
	    pts={ideal random(P2^1,P2^{-1,-2}),
	    minors(2,random(P2^3,P2^{2:-1})),
	    ideal random(P2^1,P2^{-1,-2}),ideal random(P2^1,P2^{-1,-2}),
	    minors(3,random(P2^4,P2^{3:-1}))};
	  not degree intersect pts==15) do ();
	  L=intersect apply(5,i->saturate pts_i^(i+1));
	  T=tally degrees source gens L;
	not (min keys T == {15} and  T#{15}==5)) do (count=count+1);
        H=(gens L)_{0..4};good=good+1;
	<<count;<<endl<<degree ideal H;<<endl; 
        dim ideal H !=1 and count<5^3) do (count=count+1);
    print count; 
    (pts,H)
    )
elapsedTime (pts,H)=findPoints(P2); count, good
betti (Hr=radical ideal H), degree ideal H, degree Hr
minimalBetti radical ideal H
3^7*33.6/60/60
