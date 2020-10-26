## In this document N will be a prime congruent to 3 mod 4.  Let h be the class number 
## of Q(sqrt(-N)).  Associated to this N are h Grossencharacters of infinity type (1,0) 
## ramified only at N.  Locally at N this character is ramified with order 2.  Call 
## one of these characters Psi.

#def num_cong(f,N,k,p):
#	M = ModularSymbols(N,k,1,GF(p)).cuspidal_subspace()
#	d = M.dimension()
#	for q in primes(50):
#		if (N*p)%q != 0:
#			Tq = M.hecke_operator(q)
#			M = ((Tq-ZZ(f[q]))^d).kernel()
#	return M.dimension()

##Returns space of CM forms of level N^2 and weight k if k is even and 
## of level N and weight k is k is even.
## (The Grossencharacter Psi^(k-1) is ramified at N iff k is even
def CM_space(N,k):
	assert N.is_prime() and N%4==3,"Need a prime 3 mod 4"
	K = QuadraticField(-N)
	if k%2==0:
		M = ModularSymbols(N^2,k,1).cuspidal_subspace()
	else:
		G = DirichletGroup(N,QQ)
		chi = G.0
		M = ModularSymbols(chi,k,1).cuspidal_subspace()
	for q in primes(100):
		if kronecker_symbol(K.discriminant(),q) == -1:
			d = M.dimension()
			Tq = M.hecke_operator(q)
			M = (Tq^d).kernel()
	return M

def CM_dimension(N,k):
	K = QuadraticField(-N)
	M = CM_space(N,k)
	return K.disc(),K.class_number(),M.dimension()

## Returns the generalized eigenspace of 0 of T_ell for ell split in Q(sqrt(-N))
## in level N^r and weight 2
def CM_space_modp(N,r,p,verbose=False):
	K = QuadraticField(-N)
	if verbose:
		print "Forming modular symbol space"
	M = ModularSymbols(N^r,2,1,GF(p)).cuspidal_subspace()
	for q in primes(25):
		if kronecker_symbol(K.discriminant(),q) == -1:
			d = M.dimension()
			if verbose:
				print "Computing T_",q
			Tq = M.hecke_operator(q)
			if verbose:
				print "Computing kernel"
			M = (Tq^d).kernel()
			if verbose:
				print "Dimension now is",M.dimension()
	return M

def CM_dimension_modp(N,p):
	K = QuadraticField(-N)
	M = ModularSymbols(N^2,2,1,GF(p)).cuspidal_subspace()
	for q in primes(100):
		if kronecker_symbol(K.discriminant(),q) == -1:
			d = M.dimension()
			Tq = M.hecke_operator(q)
			M = (Tq^d).kernel()
	return K.class_number(),M.dimension()


def test_minus1_modp(p):
	for q in primes(500):
		if q%4==3 and q%p==p-1:
			print(q,CM_dimension_modp(q,p))
	return "Done!"

def test_all(p,Nmin,Nmax,verbose=False):
	for q in primes(Nmin,Nmax+1):
		if q%4==3:
			if verbose:
				print "Trying",q,"which is",q%p,"mod p"
			t = CM_dimension_modp(q,p)
			if t[0]<t[1]:
				print(q,q%3,CM_dimension_modp(q,p))
	return "Done!"	

#returns the q-th Fourier coefficient of one of the (conjugate) CM forms of level N^2 and weight k
def CM_coefficient(N,k,q):
	assert N.is_prime() and N%4==3,"Need a prime congruent to 3 mod 4"
	K = QuadraticField(-N)
	if kronecker_symbol(-N,q)!=1:
		return [0]
	else:
		qq = ideal(K(q)).factor()[0][0]
		h = K.class_number()
		I = qq^h
		alpha = (I.gens_reduced()[0])^(k-1)
		alpha = alpha * kronecker_symbol(-N,alpha.real()%N)
		R.<x> = PolynomialRing(K)
		f=x^h-alpha
		facts = f.factor()
		coefs = []
		for g in facts:
			L.<b> = NumberField(g[0])
			coefs += [b + q^(k-1)/b]
		return coefs

def valuation_at_primes_over_p(alpha,p):
	K = alpha.parent()
	if K == QQ or K == ZZ:
		return [alpha.valuation(p)]
	else:
		pps = ideal(K(p)).factor()
		vals = []
		for pp in pps:
			vals += [alpha.valuation(pp[0])/pp[1]]
		return vals

#Returns L(f,1)/Omega_f for f attached to the Grossencharacter of these programs
def Lvalue_valuations(N,p):
	assert N.is_prime() and N%4==3,"Must be a prime which is 3 mod 4"
	M = CM_space(N,3)
	phi = form_modsym_from_decomposition(M)
	K = phi.base_ring()
	if K.degree()>1:
		pps = ideal(K(p)).factor()
	else:
		pps = [[p]]
	v = []
	Lval = phi.data[0].coef(0) 
	v = []
	for pp in pps:
		v += [Lval.valuation(pp[0])-phi.valuation(pp[0])]
	return v

#Runs through prime levels betweeen Nmin and Nmax which are 3 mod 4 and returns all levels
#for which L(Psi^2,1)/Omega is a non-unit mod p (for some prime over p)
def collect_levels_with_nonunit_Lvalue(Nmin,Nmax,p,verbose=false):
	levels = []
	for N in primes(Nmin,Nmax):
		if N%4==3:
			v = Lvalue_valuations(N,p)
			if max(v) > 0:
				levels += [N]
			if verbose:
				print N,v
	return levels


