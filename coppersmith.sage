"""
References:

https://www.iacr.org/archive/asiacrypt2008/53500412/53500412.pdf
https://gist.github.com/hyunsikjeong/0c26e83bb37866f5c7c6b8918a854333
https://github.com/josephsurin/lattice-based-cryptanalysis/blob/main/lbc_toolkit/problems/small_roots.sage
https://eprint.iacr.org/2023/032.pdf
"""

from sage.rings.polynomial.multi_polynomial_sequence import PolynomialSequence
import cysignals
import itertools
from tqdm import tqdm

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
    print(f"m = {m}")
    
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

def solve_system_gb(H, f, timeout=1):
    vs = list(f.variables())
    H_ = PolynomialSequence([], H[0].parent().change_ring(QQ))
    for h in tqdm(H):
        H_.append(h)
        I = H_.ideal()
        roots = []

        alarm(timeout)
        try:
            gb_solve = I.variety(ring=ZZ)
        except:
            continue
        cancel_alarm()

        for root in gb_solve:
            root = tuple(H[0].parent().base_ring()(root[var]) for var in vs)
            roots.append(root)
        return roots

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
    elif implementation == "herrmann_may":
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

def demo_1():
    N = 0xc20d4f0792f162e3f3486f47c2c5b05696ba5c81ec09f5386bf741b7289b85e2d744559825a23b0ae094da214f3158344e5d5ba86fb1ecd1f40c8682a7bee55021eba772e23793001a38b9cccbfdc1d9316cccc3b79acd045c512b44e0f3697383958113a280791e17c23fe80fa38099e4907f70f4d228285aac69ed2d3bcf99
    _p = "fe8984407b0816cc28e5ccc6bb7379??????????ca3806dd2cfdfc8d616b????????6109a4dbe3876b8d1b8adc9175dfba0e1ef318801648d6??????????a05b"
    f, bounds = generate_polynomial(N, _p)
    print(coppersmith(f, bounds, implementation="herrmann_may", algorithm="groebner", m=6, t=1))

def demo_2():
    e = 0x010001
    n = 0x00c0d76392ed01ca0729a8a0aaecbf09ee5814806fb7d0cb4fe97c81a6b48b6fd86eefdeebc71a33305f4b64c5b55b342a9dbc09ba081a2a0293e6e3b09f3f290a8c8f1c08aa28a3c830c58bc5ff97b2dc7b309e576673180ec0f8273099bc9ff84e477ade15279ca2fbc7e2df3e59dd7705e2339ca306141487a7454b6d3e7188dea6530bfee5892c0583c6132c613c0c5c1ed7f0d1a97d306fa666964bf50e11d10b3fe7d54574b815532d763979b6f5625d9823fb7c2186727197ef158bce3e3575267a79baa1819ed1d2de595ebf9ffb909b8df2a8e9efbe73f490a0cd35a4d8f02a7bd3dd5652c9d6902e75e1e9bf75df3a7da23bd7e97350b71546868161d6ab486c610471b80334745c03dac178266b32aff70fd62799f1e8da324db32fbf5b502ee45f9ff263d55f0498cfbc50b77cab263447cfcded4b5cd2ed6302276b6b69b30a4d44232c95dd2f1ae5e993577a591958b4c61ef1a9755d3641b470c127108f0a9fbe715bbc3082fe260afbeb578c229ce511a096ee492955378907
    u = 0x67a20eff99da8fd3a85d2ea87d2ff339bde448035e19cb042693608c7e630aa4a71a7c6f66b692a2c1c57169943f90947ff29fcfc3ae1bce6edf1d09600b73a952b2b34fa3d26e2a9adb84df29dda24e982de676e468a50d273c4de535bf8a11503889f339d9428fdee8f07ca7dd89768ab0ee6a72e3829514d0df9d1330be467b7999369d6699b16945a87787ea540fbc828280a23de75e573d0a6d4fb10d526b71e3a55e7b41db39d0bf773609eeaa7cc018e279aca93125c23107568e687e
    q_middle = 0xc570613da06c478
    q_lower = 0x691738dc8996d
    q_upper = 0xc597ff4fc78fabff87fd021ee21d02e2b2f726cbe12
    PR.<x0,x1> = PolynomialRing(Zmod(n), 2)
    qq = q_upper*2^(4*341) + q_middle*2^(4*116) + q_lower + 2^52*x0 + 2**524*x1
    f = u*qq**2 - qq
    print(coppersmith(f, bounds=(2^412, 2^840), implementation="shift_polynomials", algorithm="groebner", m=3, d=2))

def main():
    pass
    #demo_1()
    demo_2()

if __name__ == "__main__":
    main()
