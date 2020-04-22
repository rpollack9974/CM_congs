def num_cong(f,N,k,p):
	M = ModularSymbols(N,k,1,GF(p)).cuspidal_subspace()
	d = M.dimension()
	for q in primes(50):
		if (N*p)%q != 0:
			Tq = M.hecke_operator(q)
			M = ((Tq-ZZ(f[q]))^d).kernel()
	return M.dimension()

def CM_dimension(N):
	K = QuadraticField(-N)
	M = ModularSymbols(N^2,2,1).cuspidal_subspace()
	for q in primes(100):
		if kronecker_symbol(K.discriminant(),q) == -1:
			d = M.dimension()
			Tq = M.hecke_operator(q)
			M = (Tq^d).kernel()
	return K.disc(),K.class_number(),M.dimension()

def CM_space(N):
	K = QuadraticField(-N)
	M = ModularSymbols(N^2,2,1).cuspidal_subspace()
	for q in primes(100):
		if kronecker_symbol(K.discriminant(),q) == -1:
			d = M.dimension()
			Tq = M.hecke_operator(q)
			M = (Tq^d).kernel()
	return M

def CM_space_modp(N,p):
	K = QuadraticField(-N)
	M = ModularSymbols(N^2,2,1,GF(p)).cuspidal_subspace()
	for q in primes(100):
		if kronecker_symbol(K.discriminant(),q) == -1:
			d = M.dimension()
			Tq = M.hecke_operator(q)
			M = (Tq^d).kernel()
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


def test(p):
	for q in primes(500):
		if q%4==3 and q%p==p-1:
			print q,CM_dimension_modp(q,p)
	return "Done!"