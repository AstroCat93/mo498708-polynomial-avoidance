# Check S_r := sum_{x in F_{p^r}} (x^{p-1}-1)^{d(p^r-1)/(p-1)}  ==  -sum_{j=1}^d ((-1)^{d-j} binom(d,j))^r  (mod p)
import itertools
from math import comb
from sympy import Poly, symbols, GF
from sympy.polys.galoistools import gf_irreducible_p, gf_pow_mod, gf_mul, gf_rem, gf_sub, gf_add
from sympy.polys.domains import ZZ
X = symbols('X')
def find_irred(p, r):
    for coeffs in itertools.product(range(p), repeat=r):
        f = [1] + list(coeffs)
        if gf_irreducible_p(f, p, ZZ): return f
def S(p, r, d):
    f = find_irred(p, r)
    M = (p**r - 1)//(p-1)
    tot = [0]
    for coeffs in itertools.product(range(p), repeat=r):
        x = list(coeffs)
        while len(x) > 1 and x[0] == 0: x = x[1:]
        y = gf_pow_mod(x, p-1, f, p, ZZ)
        y = gf_sub(y, [1], p, ZZ)
        z = gf_pow_mod(y, d*M, f, p, ZZ)
        tot = gf_add(tot, z, p, ZZ)
    return tot
ok = True
for p, r in [(3,2),(3,3),(5,2),(5,3),(7,2),(11,2)]:
    for d in range(1, p):
        s = S(p, r, d)
        pred = (-sum(((-1)**(d-j)*comb(d,j))**r for j in range(1, d+1))) % p
        good = (s == ([pred] if pred else []))
        ok &= good
        print(p, r, d, s, pred, "OK" if good else "MISMATCH", flush=True)
print("ALL OK" if ok else "MISMATCH")
