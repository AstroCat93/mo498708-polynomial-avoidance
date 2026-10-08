"""C(p,d) for all primes p <= LIMIT and 0 <= d < p via
  (i)  the conjectured closed form  (-1)^{d(d+1)/2} prod_{k=0}^d binom(d,k)  mod p;
  (ii) the Newton-identity route: b_k = -sum_{s=1}^d lam_s^k, lam_s = (-1)^{d-s} binom(d,s),
       n a_n = sum_{k=1}^n b_k a_{n-k}  (n <= d <= p-1, so n is invertible mod p),
       C = (p-1) * sum_{n=0}^{d-1} a_n = -sum_{n<d} a_n  (mod p).
Checks (i) == (ii), a_n == (-1)^n e_n(lam), and C != 0 mod p.  Writes out/C_table.txt.
"""
import os, sys
from math import comb, prod
from sympy import primerange

LIMIT = int(sys.argv[1]) if len(sys.argv) > 1 else 61

def closed(p, d):
    return ((-1) ** (d * (d + 1) // 2) * prod(comb(d, k) for k in range(d + 1))) % p

def newton(p, d):
    if d == 0:
        return 1, [1]
    lam = [((-1) ** (d - s) * comb(d, s)) % p for s in range(1, d + 1)]
    b = [0] + [(-sum(pow(l, k, p) for l in lam)) % p for k in range(1, d + 1)]
    a = [1]
    for n in range(1, d + 1):
        s = sum(b[k] * a[n - k] for k in range(1, n + 1)) % p
        a.append(s * pow(n, p - 2, p) % p)
    # elementary symmetric e_n(lam)
    e = [1] + [0] * d
    for l in lam:
        for n in range(d, 0, -1):
            e[n] = (e[n] + l * e[n - 1]) % p
    for n in range(d + 1):
        assert a[n] == ((-1) ** n * e[n]) % p, (p, d, n)
    C = (-sum(a[:d])) % p
    return C, a

if __name__ == "__main__":
    lines = []; nbad = 0; nzero = 0; ncases = 0
    for p in primerange(2, LIMIT + 1):
        row = []
        for d in range(p):
            c1 = closed(p, d); c2, _ = newton(p, d)
            ncases += 1
            if c1 != c2: nbad += 1; print("MISMATCH", p, d, c1, c2)
            if c1 == 0: nzero += 1
            row.append(c1)
        lines.append(f"{p}: " + " ".join(map(str, row)))
    os.makedirs("out", exist_ok=True)
    open("out/C_table.txt", "w").write("# C(p,d) mod p for d=0..p-1 (closed form, = Newton route)\n" + "\n".join(lines) + "\n")
    print(f"cases={ncases} closed!=newton: {nbad}  zero values: {nzero}")
