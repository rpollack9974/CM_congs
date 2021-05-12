def get_cuspidal_modp_modsym_space(p,N,k,neben=-1,newforms=false,G1=false):
	if neben == -1 and G1 == false:
		M = ModularSymbols(N,k,1,GF(p))
	else:
		if neben != -1:
			M = ModularSymbols(neben,k,1,GF(p))
		else: 
			M = ModularSymbols(Gamma1(N),k,1,GF(p))
	M = M.cuspidal_subspace()
	if newforms:
		M = M.new_subspace()

	return M


def mod_p_reductions(p,N,k,neben=-1,newforms=true,G1=false,verbose=false,p_bound=25,Fp=true):
	rbs = []
	mults = []
	M = get_cuspidal_modp_modsym_space(p,N,k,neben=neben,newforms=newforms,G1=G1)
	As = M.decomposition()

	return As

def mult(A,p_bound=25):
	ans_e = []
	ans_f = []
	p = A.base_ring().characteristic()
	N = A.level()
	for ell in primes(p_bound):
			if gcd(ell,N*p) == 1:
				h = A.hecke_polynomial(ell).factor()
				e = h[0][1]
				f = h[0][0].degree()
				ans_e += [e]
				ans_f += [f]

	return min(ans_e),max(ans_f)

def rb(A,p_bound=25):
	ans = []
	p = A.base_ring().characteristic()
	N = A.level()
	for ell in primes(p_bound):
			if gcd(ell,N*p) == 1:
				f = A.hecke_polynomial(ell).factor()[0][0]
				if f.degree() > 1:
					ans += [[ell,A.hecke_polynomial(ell).factor()[0][0]]]
				else:
					ans += [[ell,f.roots()[0][0]]]
	return ans

def data(As,p_bound=25):
	for A in As:
		print rb(A),mult(A)

def rb_twist(A,chi,p_bound=25):
	ans = []
	p = A.base_ring().characteristic()
	N = A.level()
	for ell in primes(p_bound):
			if gcd(ell,N*p) == 1:
				f = A.hecke_polynomial(ell).factor()[0][0]
				R = f.parent()
				x = R.gens()[0]
				f = f.substitute(chi(ell)*x)
				f = f/f.leading_coefficient()
				if f.degree() > 1:
					ans += [[ell,A.hecke_polynomial(ell).factor()[0][0]]]
				else:
					ans += [[ell,f.roots()[0][0]]]
	return ans

def is_congtwist(p,N,A,As):
	j = -1
	twist = false
	f = multiplicative_order(mod(p,euler_phi(N)))
	G = DirichletGroup(N,GF(p^f))
	chi = G.0
	while j < len(As)-1 and not twist:
		j += 1
		B = As[j]
		for e in range(chi.order()):
			if rb_twist(B,chi^e) == rb(A):
				twist = true
	return twist,B,chi^e

def is_eisen(p,N,A):
	if mult(A)[1] != 1:
		return false
	else:
		r = rb(A)
		eisen = true
		for i in range(len(r)):
			ell = r[i][0]
			aell = r[i][1]
			eisen = eisen and aell%p==(ell+1)%p
	return eisen

def is_eisentwist(p,N,A):
	G = DirichletGroup(N,GF(p))
	chi = G.0
	if mult(A)[1] != 1:
		return false
	else:
		r = rb(A)
		eisen = true
		for i in range(len(r)):
			ell = r[i][0]
			aell = r[i][1]
			eisen = eisen and aell%p==(chi(ell)*(ell+1))%p
	return eisen

def analyze_data(p,N,As1,As2):
	for j in range(len(As2)):
		A = As2[j]
		print("Rhobar #%s:" % (j+1))
		print("--%s" % rb(A))
		m = mult(A)
		print("--multiplicity=%s and conjugates=%s" % (m[0],m[1]))
		twist,B,psi = is_congtwist(p,N,A,As1)
		if twist:
			print("*****Congruent to a twist from level %s" % N)
		if is_eisen(p,N,A):
			print("*****Congruent to an Eisenstein series")
		if is_eisentwist(p,N,A):
			print("*****Congruent to a twist of Eisenstein series")
		print "--------------------------------------"

	return "done"

def compute_and_analyze_data(p,N):
	As1 = mod_p_reductions(p,N,2,G1=true)
	As2 = mod_p_reductions(p,N^2,2)
	analyze_data(p,N,As1,As2)

