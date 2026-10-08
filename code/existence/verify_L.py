# Verify: Lbar_d(u) = sum_{m monic} N(m)^d u^{deg m}  (N(m)=prod_{a in F_p^*} m(a))
# equals G_d(u) = prod_{j=1}^d (1 - (-1)^{d-j} binom(d,j) u)  in F_p[u] modulo u^p  (for 1<=d<=p-1),
# by brute force over monic m of degree k <= p-1 (when feasible).
import itertools, sys
from math import comb
import numpy as np

def A_coeffs(p, d, kmax):
    # A_k = sum over monic m of degree k of N(m)^d mod p
    res = []
    pts = np.arange(1, p, dtype=np.int64)
    for k in range(kmax+1):
        if p**k > 2e7: res.append(None); continue
        n = p**k
        idx = np.arange(n, dtype=np.int64)
        # coefficients m_0..m_{k-1}
        vals = np.zeros((n, p-1), dtype=np.int64)
        # m(a) = a^k + sum_j m_j a^j
        for ai, a in enumerate(range(1, p)):
            v = np.full(n, pow(a, k, p), dtype=np.int64)
            for j in range(k):
                mj = (idx // p**j) % p
                v = (v + mj * pow(a, j, p)) % p
            vals[:, ai] = v
        N = np.ones(n, dtype=np.int64)
        for ai in range(p-1):
            N = (N * vals[:, ai]) % p
        Nd = np.ones(n, dtype=np.int64)
        for _ in range(d):
            Nd = (Nd * N) % p
        res.append(int(Nd.sum() % p))
    return res

def G_coeffs(p, d):
    poly = [1]
    for j in range(1, d+1):
        lam = ((-1)**(d-j) * comb(d, j)) % p
        new = [0]*(len(poly)+1)
        for i, c in enumerate(poly):
            new[i] = (new[i] + c) % p
            new[i+1] = (new[i+1] - lam*c) % p
        poly = new
    return poly

allok = True
for p in [3,5,7,11,13]:
    for d in range(1, p):
        kmax = p-1
        A = A_coeffs(p, d, kmax)
        G = G_coeffs(p, d) + [0]*(kmax+1)
        ok = all(A[k] is None or A[k] == G[k] % p for k in range(kmax+1))
        allok &= ok
        print(p, d, "A=", A, "G=", G[:kmax+1], "OK" if ok else "MISMATCH", flush=True)
print("ALL OK" if allok else "SOME MISMATCH")
