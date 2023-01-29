"""
References:

https://www.iacr.org/archive/asiacrypt2008/53500412/53500412.pdf
https://gist.github.com/hyunsikjeong/0c26e83bb37866f5c7c6b8918a854333
https://github.com/josephsurin/lattice-based-cryptanalysis/blob/main/lbc_toolkit/problems/small_roots.sage
https://eprint.iacr.org/2023/032.pdf
"""

from sage.rings.polynomial.multi_polynomial_sequence import PolynomialSequence
from Crypto.Util.number import getPrime
from tqdm import tqdm
import cysignals
import itertools

def generate_polynomial(N, _p):
    coefficients = []
    bounds = []
    i = 0
    ii = 0
    is_previous_unknown = True if _p[-1] == '?' else False

    for char in _p[::-1]:
        is_current_unknown = True if char == '?' else False
        if is_current_unknown and not is_previous_unknown:
            coefficients.append(2^(4*ii))
            i = 0
        if not is_current_unknown and is_previous_unknown:
            bounds.append(2^(4*i))
        is_previous_unknown = is_current_unknown
        i += 1
        ii += 1

    if is_current_unknown:
        bounds.append(2^(4*i))
        coefficients = coefficients[::-1]
        coefficients.append(1)

    d = len(coefficients)
    xs = [f"x{i}" for i in range(d)]
    PR = PolynomialRing(Zmod(N), d, xs)
    f = int(_p.replace("?", "0"), 16) + sum([c * PR.objgens()[1][n] for n, c in enumerate(coefficients)])
    return f, bounds[::-1]

def univariate(f, X, beta=1.0, m=None):
    N = f.parent().characteristic()
    delta = f.degree()
    if m is None:
        epsilon = RR(beta^2/f.degree() - log(2*X, N))
        m = max(beta**2/(delta * epsilon), 7*beta/delta).ceil()
    t = int((delta*m*(1/beta - 1)).floor())
    #print(f"m = {m}")
    
    f = f.monic().change_ring(ZZ)
    P,(x,) = f.parent().objgens()
    g  = [x**j * N**(m-i) * f**i for i in range(m) for j in range(delta)]
    g.extend([x**i * f**m for i in range(t)]) 
    B = Matrix(ZZ, len(g), delta*m + max(delta,t))

    for i in range(B.nrows()):
        for j in range(g[i].degree()+1):
            B[i,j] = g[i][j]*X**j

    B =  B.LLL()
    f = sum([ZZ(B[0,i]//X**i)*x**i for i in range(B.ncols())])
    roots = set([f.base_ring()(r) for r,m in f.roots() if abs(r) <= X])
    return [root for root in roots if N.gcd(ZZ(f(root))) >= N**beta]

def solve_system_jacobian(h, f, bounds, iters=200, prec=1000):
    n = f.nvariables()
    x = f.parent().objgens()[1]
    x_ = [var(f'x{i}') for i in range(n)]
    for ii in Combinations(range(len(h)), k=n):
        f = symbolic_expression([h[i](x) for i in ii]).function(x_)
        jac = jacobian(f, x_)
        v = vector([t // 2 for t in bounds])
        for _ in tqdm(range(iters)):
            kwargs = {'x{}'.format(i): v[i] for i in range(n)}
            try:
                tmp = v - jac(**kwargs).inverse() * f(**kwargs)
            except ZeroDivisionError:
                return None
            v = vector((numerical_approx(d, prec=prec) for d in tmp))
        v = [int(_.round()) for _ in v]
        if h[0](v) == 0:
            return v
    return None

def solve_system_gb(H, f, timeout=2):
    vs = list(f.variables())
    H_ = PolynomialSequence([], H[0].parent().change_ring(QQ))
    for h in tqdm(H):
        H_.append(h)
        I = H_.ideal()
        roots = []

        alarm(timeout)
        try:
            for root in I.variety(ring=ZZ):
                root = tuple(H[0].parent().base_ring()(root[var]) for var in vs)
                roots.append(root)
            cancel_alarm()
            return roots
        except:
            cancel_alarm()       

class IIter:
    def __init__(self, m, n):
        self.m = m
        self.n = n
        self.arr = [0 for _ in range(n)]
        self.sum = 0
        self.stop = False

    def __iter__(self):
        return self

    def __next__(self):
        if self.stop:
            raise StopIteration
        ret = tuple(self.arr)
        self.stop = True
        for i in range(self.n - 1, -1, -1):
            if self.sum == self.m or self.arr[i] == self.m:
                self.sum -= self.arr[i]
                self.arr[i] = 0
                continue

            self.arr[i] += 1
            self.sum += 1
            self.stop = False
            break
        return ret

def multivariate_herrmann_may(f, bounds, m, t):
    n = f.nvariables()
    N = f.base_ring().cardinality()
    f /= f.coefficients().pop(0)  
    f = f.change_ring(ZZ)
    x = f.parent().objgens()[1]

    g = []
    monomials = []
    Xmul = []
    for ii in IIter(m, n):
        k = ii[0]
        g_tmp = f^k * N^max(t-k, 0)
        monomial = x[0]^k
        Xmul_tmp = bounds[0]^k
        for j in range(1, n):
            g_tmp *= x[j]^ii[j]
            monomial *= x[j]^ii[j]
            Xmul_tmp *= bounds[j]^ii[j]
        g.append(g_tmp)
        monomials.append(monomial)
        Xmul.append(Xmul_tmp)

    B = Matrix(ZZ, len(g), len(g))
    for i in range(B.nrows()):
        for j in range(i + 1):
            if j == 0:
                B[i, j] = g[i].constant_coefficient()
            else:
                v = g[i].monomial_coefficient(monomials[j])
                B[i, j] = v * Xmul[j]

    print("LLL...")
    B = B.LLL()
    print("LLL done")

    h = []
    for i in range(B.nrows()):
        h_tmp = 0
        for j in range(B.ncols()):
            if j == 0:
                h_tmp += B[i, j]
            else:
                assert B[i, j] % Xmul[j] == 0
                v = ZZ(B[i, j] // Xmul[j])
                h_tmp += v * monomials[j]
        h.append(h_tmp)
   
    return f, h

def multivariate_shift_polynomials(f, bounds, m=1, d=None):
    if d is None:
        d = f.degree()

    R = f.base_ring()
    N = R.cardinality()
    f_ = (f // f.lc()).change_ring(ZZ)
    f = f.change_ring(ZZ)
    l = f.lm()

    M = []
    for k in range(m+1):
        M_k = set()
        T = set((f ^ (m-k)).monomials())
        for mon in (f^m).monomials():
            if mon//l^k in T: 
                for extra in itertools.product(range(d), repeat=f.nvariables()):
                    g = mon * prod(map(power, f.variables(), extra))
                    M_k.add(g)
        M.append(M_k)
    M.append(set())

    shifts = PolynomialSequence([], f.parent())
    for k in range(m+1):
        for mon in M[k] - M[k+1]:
            g = mon//l^k * f_^k * N^(m-k)
            shifts.append(g)

    B, monomials = shifts.coefficient_matrix()
    monomials = vector(monomials)

    factors = [monomial(*bounds) for monomial in monomials]
    for i, factor in enumerate(factors):
        B.rescale_col(i, factor)

    print("LLL...")
    B = B.dense_matrix().LLL()
    print("LLL done")

    B = B.change_ring(QQ)
    for i, factor in enumerate(factors):
        B.rescale_col(i, 1/factor)
    B = B.change_ring(ZZ)

    H = PolynomialSequence([h for h in B*monomials if not h.is_zero()])
    return f, H

def multivariate(f, bounds, implementation, algorithm, m=1, t=1, d=None):
    if implementation == "herrmann_may":
        f, h = multivariate_herrmann_may(f, bounds, m, t)
    elif implementation == "shift_polynomials":
        f, h = multivariate_shift_polynomials(f, bounds, m, d)
    else:
        print("invalid implementation")
        return None

    if algorithm == "jacobian":
        return solve_system_jacobian(h, f, bounds)
    elif algorithm == "groebner":
        return solve_system_gb(h, f)
    else:
        print("invalid algorithm")
        return None

def recover_p_high(p_high, n):
    p_bits = (len(bin(n))-2)//2
    p_high_bits = len(bin(p_high)) - 2
    PR.<x> = PolynomialRing(Zmod(n))
    f = p_high * 2**(p_bits-p_high_bits) + x
    x = univariate(f, X=2**(p_bits-p_high_bits), beta=0.4)
    if x == []:
        return None
    p = int(f(x[0]))
    if is_prime(p):
        return p
    return None

def recover_p_low(p_low, n):
    p_bits = (len(bin(n))-2)//2
    p_low_bits = len(bin(p_low)) - 2
    PR.<x> = PolynomialRing(Zmod(n))
    f = x * 2**p_low_bits + p_low
    x = univariate(f, X=2**(p_bits-p_low_bits), beta=0.4)
    if x == []:
        return None
    p = int(f(x[0]))
    if is_prime(p):
        return p
    return None

def demo_1():
    p = getPrime(512)
    q = getPrime(512)
    n = p*q
    p_high = int(hex(p)[:100], 16)
    print("\ndemo 1 - p_high")
    if recover_p_high(p_high, n) is not None:
        print("PASS")
    else:
        print("FAIL")

def demo_2():
    p = getPrime(512)
    q = getPrime(512)
    n = p*q
    p_low = int(hex(p)[-100:], 16) 
    print("\ndemo 2 - p_low")
    if recover_p_low(p_low, n) is not None:
        print("PASS")
    else:
        print("FAIL")

def demo_3():
    # not 100% successful and very slow unless e is small
    def recover_d_low(d_low, n, e):
        t = len(bin(d_low)) - 2
        for k in tqdm(range(1, e)):
            x = var('x')
            for r in solve_mod([x*e*d_low == x + k*(n*x - x**2 - n + x)], 2**t):
                p_low = int(r[0])
                try:
                    p = recover_p_low(p_low, n)
                    if p is not None and is_prime(p):
                        return p
                except:
                    continue

    while True:
        p = getPrime(256)
        q = getPrime(256)
        e = 11
        n = p*q
        try:
            d = int(pow(e, -1, (p-1)*(q-1)))
            break
        except ZeroDivisionError:
            continue

    d_low = int(hex(d)[80:], 16)
    print("\ndemo 3 - d_low")
    if recover_d_low(d_low, n, e) is not None:
        print("PASS")
    else:
        print("FAIL")

def demo_4():
    def recover_dp_high(dp_high, n, e):
        beta = 0.4
        upper_bound = int(2*n**(beta**2))
        dp_bits_max = (len(bin(n))-2)//2
        for dp_bits in range(dp_bits_max + 1, dp_bits_max - 20, -1):
            _dp = int(dp_high * 2**(dp_bits - (len(bin(dp_high))-2)))
            for xi in range(-upper_bound + upper_bound//8, upper_bound, upper_bound//4):
                P.<x> = PolynomialRing(Zmod(n))
                f = _dp*e + x - xi
                x = f.small_roots(X=upper_bound, beta=beta)
                if x == []:
                    continue
                kp = int(f(x[0]))
                p = gcd(n, kp)
                if 1 < p < n and is_prime(p):
                    return p

    p = getPrime(512)
    q = getPrime(512)
    n = p*q
    e = 65537
    d = pow(e, -1, (p-1)*(q-1))
    dp = int(d % (p-1))
    dp_high = int(hex(dp)[:100], 16)
    print("\ndemo 4 - dp_high")
    if recover_dp_high(dp_high, n, e) is not None:
        print("PASS")
    else:
        print("FAIL")


def main():
    demo_1()
    demo_2()
    demo_3()
    demo_4()

if __name__ == "__main__":
    main()
