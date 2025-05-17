loadPackage "BGG"
loadPackage "AdjunctionForSurfaces"
loadPackage "NongeneralTypeSurfacesInP4" 

p = 2
KK = ZZ/p
E = KK[e_0..e_4, SkewCommutative => true]
smoothBordiga = N -> ( -- N is the number of 4x3 matrices we choose randomly. The command collects the ones defining Bordiga surfaces
   i := 0;
   L := {};
   while i < N 
   do (
	bd := random(E^{4:0},E^{3:-1});
   	KK := coefficientRing E;
   	ext := KK[first entries vars E];
   	a := sub(bd,ext);
   	nrows := rank source a;
   	dv := minors(nrows,a);
   	cd := codim dv;
   	sdv := singularLocus dv;
   	cds := codim sdv;
    	if cd == 2 and cds == 5 then (
	    L = append(L,bd);
	    );
	i = i+1;
	);
   L
   )


L = smoothBordiga(10000); 

-- The command below attempts to find a monad of the ideal sheaf of a nonsingular surface
-- with degree 12, sectional genus 13, and Euler characteristic 2. It uses a 4x3 matrix with
-- linear entries to find such a monad.  

randomMonad = (N,B) -> (
   i := 0;
   isSmooth := false;
   symbol x;
   R := KK[x_0..x_4];
   L := {};
   while i < N and not isSmooth do (
	stB := syz transpose B;
	phi := transpose stB;
	r := random(E^{8:2},target phi);
	psi := r*phi;
	spsi := syz psi;
	if (tally degrees source spsi)_{1} == 3 and 
	(tally degrees source spsi)_{2} == 1 and 
	(tally degrees source spsi)_{3} == 0 then (
	    tau := syz spsi;
	    if (tally degrees source tau)_{3} == 3 and (tally degrees source tau)_{4} == 5 then (
		beta := spsi;
		alpha' := submatrix(tau,,{0,1,2});
		alpha'' := submatrix(tau,,{3,4,5,6,7});		    
	    	alpha := alpha' | (alpha''*random(source alpha'',E^{1:-4}));
		beta = beilinson(beta,R);
		alpha = beilinson(alpha,R);
		F := prune homology(beta, alpha);
		<< betti presentation F << endl;
		delta := syz transpose presentation F;
		<< betti delta << endl;
		if rank source delta == 1 then (
		    I := ideal (delta);
		    dg := degree I;
		    cd := codim I;
		    sI := singularLocus I;
		    cds := codim sI;
		    << "codimension of the singularity = " << cds << endl;
		    if dg == 12 and cd == 2 and cds == 5 then (
			isSmooth = true;
			L = append(L,I);
			);
		    );
		);
	    );
   i = i+1;
   );
L)

-- Below, we run the command for each 3x4 matrix collected.
-- The number of trials for each matrix must be large.
-- Based on my observation, I recommend N = 2^18 to make suare
-- we get a positive number of nonsingular surfaces. 

M = {}
for i from 0 to #L-1 do (
    << " -- No." << i << endl;
    I := randomMonad(2^18,L#i);
    if I != {} then (
	M = append(M,I);
	);
    )
