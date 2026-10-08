# Direct symbolic check (independent of the reductions): C = coeff of c0^d prod_{j=1}^d c_j^{p-1}
# in prod_{i in F_p} (sum_j c_j i^j)^d over F_p, vs (-1)^{d(d+1)/2} prod_k binom(d,k) mod p.
from sympy import symbols, Poly, GF
from math import comb, prod
import sys
def C_direct(p, d):
    c = symbols('c0:%d' % (d+1))
    P = Poly(1, *c, modulus=p)
    for i in range(p):
        L = Poly(sum(c[j]*pow(i, j, p) for j in range(d+1)), *c, modulus=p)
        P = P * L**d
    mon = tuple([d] + [p-1]*d)
    return P.as_dict().get(mon, 0) % p
def closed(p, d):
    return ((-1)**(d*(d+1)//2) * prod(comb(d, k) for k in range(d+1))) % p
ok = True
for p, dmax in [(3,2),(5,4),(7,4),(11,3),(13,2)]:
    for d in range(0, dmax+1):
        a, b = C_direct(p, d), closed(p, d)
        ok &= (a == b)
        print(p, d, a, b, "OK" if a == b else "MISMATCH", flush=True)
print("ALL OK" if ok else "MISMATCH")
