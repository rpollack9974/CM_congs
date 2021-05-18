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
function mults(Ms,p:p_bound:=25,aell_output:=true,check_twists:=false,twist_data:=-1,verbose:=false)
	v := [];
	for M in Ms do
		m := mult(M);
		v := v cat [m];
		if verbose then
			print m;
		end if;

		if aell_output or check_twists then
			fcs := FC(M:exclude:=p);
		end if;
		if aell_output then
			print fcs;
		end if;

		if check_twists then
			if Position(twist_data[1],fcs) gt 0 then
				if verbose then
					print "eisenstein";
				end if;
				v[#v] := v[#v] cat [-2];
			else
				if Position(twist_data[2],fcs) gt 0 then
					if verbose then
						print "twists to lower level cuspidal congruence";
					end if;
					v[#v] := v[#v] cat [-1];
				end if;
			end if;
		end if;
	end for;
	v:=Reverse(Sort(v));

	return v;
end function;

function new_cuspidal_modp_subspace(p,N)
	return NewSubspace(CuspidalSubspace(ModularSymbols(N,2,GF(5),1)));
end function;


function twists_to_level_Nsquared(p,N:p_bound:=25,max_degree:=Infinity(),verbose:=false)
	e := Order(Integers(N-1)!p);
	G := DirichletGroup(N,GF(p^e));
	psi := G.1;
	chi := psi^((N-1) div 2);
	triv := psi^(N-1);

//Eisenstein first
	eisen := [**];
	for a in [1..N-1] do
		if a mod 2 eq 0 then
			chis := [[triv,psi^a],[psi^a,triv],[chi,chi*psi^a],[chi*psi^a,chi]];
			for pair in chis do
				v := [];
				poly := false;
				for q in [1..p_bound] do
					if IsPrime(q) and Gcd(q,N*p) eq 1 then
						aq := pair[1](q) * q + pair[2](q);
						f := MinimalPolynomial(aq);
						f := abs_poly(f);
						poly := poly or Degree(f) gt 1;
						if poly then
							v := v cat [<q,f>];
						else
							v := v cat [<q,aq>];
						end if;
					end if;
				end for;
				eisen := eisen cat [*v*];
				if verbose then
					print a;
					print v;
				end if;
			end for;
		end if;
	end for;

	ans := [**];
	for a in [1..N-1] do
		if a mod 2 eq 0 then
			M := NewSubspace(CuspidalSubspace(ModularSymbols(psi^a,2,1)));
			As := decomposition(M);
			for B in As do
				if max_degree ge degree_of_field_of_definition(B:twist:=psi^(a div 2)) then
					a1 := FC(B:p_bound:=p_bound,twist:=psi^(-a div 2),exclude:=p);
					a2 := FC(B:p_bound:=p_bound,twist:=psi^(-a div 2) * psi^((N-1) div 2),exclude:=p);
					ans := ans cat [*a1,a2*];
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


procedure find_mults_at_level_Nsquared(p,Nmin,Nmax:aell_output:=false,p_bound:=25,check_twists:=true,verbose:=false)
	for N in [Nmin..Nmax] do
		if IsPrime(N) and N mod p eq p-1 then
			if check_twists then
				eisen,cusps := twists_to_level_Nsquared(p,N:p_bound:=p_bound);
				Mtwist := [*eisen,cusps*];
			else
				Mtwist := -1;
			end if;
			M := new_cuspidal_modp_subspace(p,N^2);
			print "Level",N;
			D := decomposition(M);
			print mults(D,p:check_twists:=check_twists,twist_data:=Mtwist,aell_output:=aell_output,verbose:=verbose);
		end if;
	end for;
end procedure;
