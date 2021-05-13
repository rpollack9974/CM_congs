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

//does mult for each ModSym space in the list Ms
function mults(Ms:p_bound:=25,aell_output:=true)
	if aell_output then
		for M in Ms do
			print mult(M),FC(M);
		end for;
	end if;
	v:=[mult(M) : M in Ms];
	v:=Reverse(Sort(v));

	return v;
end function;

function FC(M:p_bound:=25)
	fcs := [];
	for ell in [1..p_bound] do
		if IsPrime(ell) and Gcd(ell,Level(M)) eq 1 then
			fell := Factorization(HeckePolynomial(M,ell))[1][1];
			if Degree(fell) gt 1 then
				fcs := fcs cat [<ell,fell>];
			else
				fcs := fcs cat [<ell,Roots(fell)[1][1]>];
			end if;
		end if;
	end for;

	return fcs;
end function;

function main_space(p,N)
	return NewSubspace(CuspidalSubspace(ModularSymbols(N^2,2,GF(5),1)));
end function;

procedure find_mults(p,Nmin,Nmax:aell_output:=false)
	for N in [Nmin..Nmax] do
		if IsPrime(N) and N mod p eq p-1 then
			M := main_space(p,N);
			print "Level",N;
			D := decomposition(M);
			print mults(D:aell_output:=aell_output);
		end if;
	end for;
end procedure;
			