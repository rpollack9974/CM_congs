function pth_power_list(v,p)
	return [v[a]^p : a in [1..#v]];
end function;

function abs_poly(f)
	ans := f;
	R := Parent(f);
	p := Characteristic(BaseRing(Parent(f)));
	v := Coefficients(f);
	v := pth_power_list(v,p);
	while R!v ne f do
		ans := ans * R!v;
		v := pth_power_list(v,p);
	end while;
	return ans;
end function;

//alpha in Fpbar returns n such that alpha is in F_p^n and not smaller
function min_degree(alpha)
	if alpha eq 0 then
		return 1;
	else
		p := Characteristic(Parent(alpha));
		t := 1;
		found := false;
		while not found do
			found := alpha^(p^t-1) eq 1;
			t := t + 1;
		end while;

		return t-1;
	end if;
end function;

//Takes a list of modsym spaces and returns a longer list gotten by decomposing each space 
//in the original list by T_ell
function decomposition_at_ell(Ms,ell:p_bound:=25)
	ans := [**];
	for M in Ms do
		Tl := HeckeOperator(M,ell);
		fl := CharacteristicPolynomial(Tl);
		fls := Factorization(fl);
		for g in fls do
			h := g[1]^g[2];
			I := [<ell,h>];
			newM := Kernel(I,M);
			ans := ans cat [*newM*];
		end for;
	end for;

	return ans;
end function;

//Takes a list of (or a single) modsym space(s) and returns a list of "simple" modsym spaces;
//that is, char(T_ell) on each space should be a power of an irreducible poly.
function decomposition(Ms:p_bound:=25,verbose:=false)
	if Type(Ms) eq ModSym then
		Ms := [Ms];
	end if;
	ans := Ms;
	for ell in [1..p_bound] do
		if IsPrime(ell) and Gcd(Level(Ms[1]),ell) eq 1 then
			if verbose then
				print "Working on ell =",ell;
			end if;
			ans := decomposition_at_ell(ans,ell:p_bound:=p_bound);
		end if;
	end for;
	return ans;
end function;

//returns the "multiplicity" and "how many conjugates" of a space of modular symbols;
//that is, multiplicity, is the lowest exponent e such that char(T_ell) = f_ell^e,
//while "number of conjugates" is the maximal degree of f_ell (an irred poly over F_p)
function mult(M:p_bound:=25)
	ms:=[];
	fs:=[];
	for ell in [1..p_bound] do
		if IsPrime(ell) and Gcd(Level(M),ell) eq 1 then
			fl := HeckePolynomial(M,ell);
			gs := Factorization(fl);
			ms := ms cat [gs[1][2]];
			fs := fs cat [Degree(gs[1][1])];
		end if;
	end for;
	return [Min(ms),Max(fs)];
end function;

//M should be Hecke simple --- returns the Fourier coefficients
function FC(M:p_bound:=25,twist:=0,exclude:=1)
	fcs := [];
	for ell in [1..p_bound] do
		if IsPrime(ell) and Gcd(ell,Level(M)*exclude) eq 1 then
			fell := Factorization(HeckePolynomial(M,ell))[1][1];
			R := Parent(fell);
			AssignNames(~R,["T"]);
			if Type(twist) eq GrpDrchElt then
				x := Random(Generators(Parent(fell)));
				fell := Evaluate(fell,twist(ell)^(-1)*x);
				fell := fell / LeadingCoefficient(fell);
			end if;
			fell := abs_poly(fell);
			if Degree(fell) gt 1 then
				fcs := fcs cat [<ell,fell>];
			else
				fcs := fcs cat [<ell,Roots(fell)[1][1]>];
			end if;
		end if;
	end for;

	return fcs;
end function;

function degree_of_field_of_definition(M:p_bound:=25,verbose:=false,twist:=-1)
	fcs := [];
	v := [];
	for ell in [1..p_bound] do
		if IsPrime(ell) and Gcd(ell,Level(M)) eq 1 then
			fell := Factorization(HeckePolynomial(M,ell))[1][1];
			if Type(twist) eq GrpDrchElt then
				x := Random(Generators(Parent(fell)));
				fell := Evaluate(fell,twist(ell)^(-1)*x);
				fell := fell / LeadingCoefficient(fell);
			end if;
			c := Coefficients(fell);
			a := Max([min_degree(c[a]) : a in [1..#c]]);
			f := Degree(fell);
			v := v cat [f * a];
			if verbose then
				print ell,fell;
		 	end if;
		end if;
	end for;

	return Max(v);
end function;

//does mult for each ModSym space in the list Ms
function mults(Ms,p:p_bound:=25,aell_output:=true,check_twists:=false,twist_data:=-1,verbose:=false,include_old:=true,old_data:=-1)
	v := [**];
	cusp_twist := false;
	for M in Ms do
		str := "---";
		md := "---";
		m := mult(M);
		fcs := FC(M:exclude:=p);
		if verbose then
			print m;
		end if;
		if aell_output then
			print fcs;
		end if;
		if check_twists then
			if Position(twist_data[1],fcs) gt 0 then
				if verbose then
					print "eisenstein";
				end if;
				str := "eisen";
			else
				td := [twist_data[2][a][1] : a in [1..#twist_data[2]]];
				j := Position(td,fcs);
				if j gt 0 then
					if verbose then
						print "twists to lower level cuspidal congruence";
					end if;
					str := "cusp_twist";
					md := twist_data[2][j][2];
				end if;
			end if;			
		end if;
		v := v cat [*[*m,fcs,str,md*]*];
	end for;

	if include_old then
		if verbose then
			print "working through level N";
		end if;
		FCs := [v[a][2] : a in [1..#v]];
		for M in old_data do
			m := mult(M);
			fcs := FC(M:exclude:=p);
			if verbose then
				print m;
			end if;
			if aell_output then
				print fcs;
			end if;
			a := Position(FCs,fcs);
			if a gt 0 then
				v[a][1][1] := v[a][1][1] + m[1];
				v[a][3] := v[a][3] cat ": old added";
			end if;
		end for;
	end if;

	muls := [v[a][1] : a in [1..#v]];
	muls:=Reverse(Sort(muls));

	return v,muls;
end function;

function new_cuspidal_modp_subspace(p,N)
	return NewSubspace(CuspidalSubspace(ModularSymbols(N,2,GF(p),1)));
end function;


function twists_to_level_Nsquared(p,N:p_bound:=25,max_degree:=Infinity(),verbose:=false)
	e := Order(Integers(N-1)!p);
	G := DirichletGroup(N,GF(p^e));
	psi := G.1;
	chi := psi^((N-1) div 2);
	triv := psi^(N-1);

//Eisenstein first
	eisen := [**];
	for a in [0..N-2] do
		if a mod 2 eq 0 then
			chis := [[triv,psi^a],[psi^a,triv],[chi,chi*psi^a],[chi*psi^a,chi]];
			for pair in chis do
				v := [];
				need_poly := false;
				for q in [1..p_bound] do
					if IsPrime(q) and Gcd(q,N*p) eq 1 then
						aq := pair[1](q) * q + pair[2](q);
						f := MinimalPolynomial(aq);
						f := abs_poly(f);
						need_poly := need_poly or Degree(f) gt 1;
						v := v cat [<q,f>];
					end if;
				end for;
				if not need_poly then
					w := [];
					for t in v do
						w := w cat [<t[1],Roots(t[2])[1][1]>];
					end for;
					v := w;
				end if;
				eisen := eisen cat [*v*];
				if verbose then
					print a;
					print v;
				end if;
			end for;
		end if;
	end for;

	ans := [**];
	for a in [0..N-2] do
		if a mod 2 eq 0 then
			M := NewSubspace(CuspidalSubspace(ModularSymbols(psi^a,2,1)));
			As := decomposition(M);
			for B in As do
				if max_degree ge degree_of_field_of_definition(B:twist:=psi^(a div 2)) then
					a1 := FC(B:p_bound:=p_bound,twist:=psi^(-a div 2),exclude:=p);
					a2 := FC(B:p_bound:=p_bound,twist:=psi^(-a div 2) * psi^((N-1) div 2),exclude:=p);
					ans := ans cat [*[*a1,[*Order(psi^a),"---"*]*],[*a2,[*Order(psi^a),"twist"*]*]*];
					if verbose then
						print "******* a =",a;
						print a1;
						print a2;
					end if;
				end if;
			end for;
		end if;
	end for;

	return eisen,ans;
end function;

function mults_at_level_Nsquared(p,N:aell_output:=false,p_bound:=25,check_twists:=true,verbose:=false,include_old:=true)
	if check_twists then
		eisen,cusps := twists_to_level_Nsquared(p,N:p_bound:=p_bound);
		Mtwist := [*eisen,cusps*];
	else
		Mtwist := -1;
	end if;
	M := new_cuspidal_modp_subspace(p,N^2);
	print(M);
	print "Level",N^2;
	D := decomposition(M);
	if include_old then
		Mold := new_cuspidal_modp_subspace(p,N);
		Dold := decomposition(Mold);
	else
		Dold := -1;
	end if;
	a,b := mults(D,p:check_twists:=check_twists,twist_data:=Mtwist,aell_output:=aell_output,verbose:=verbose,include_old:=include_old,old_data:=Dold);
	return a,b;
end function;

procedure collect_mults_at_level_Nsquared(p,Nmin,Nmax:aell_output:=false,p_bound:=25,check_twists:=true,verbose:=false,include_old:=true)
	for N in [Nmin..Nmax] do
		if IsPrime(N) and N mod p eq p-1 then
			a,b := mults_at_level_Nsquared(p,N:aell_output:=aell_output,p_bound:=p_bound,check_twists:=check_twists,verbose:=verbose,include_old:=include_old);
			print a,b;
		end if;
	end for;
end procedure;

function multiplicity_rhobar_in_space(rb,M:verbose:=false)
	p := Characteristic(BaseRing(M));
	N := Level(M);
	D := decomposition(M:verbose:=verbose);
	ans := 0;
	for A in D do
		found := true;
		i := 1;
		while found and i le #rb do
			ell := rb[i][1];
			if Gcd(ell,N*p) eq 1 then
				g_ell := rb[i][2];
				f_ell := Factorization(HeckePolynomial(A,ell))[1][1];
				if Type(g_ell) eq FldFinElt then
					a_ell := Roots(f_ell)[1][1];
					found := found and a_ell eq g_ell;
				else
					found := found and f_ell eq g_ell;
				end if;
			end if;
			i := i + 1;
		end while;
		if found then
			ans := ans + Dimension(A) div Degree(f_ell);
		end if;
	end for;

	return ans;
end function;