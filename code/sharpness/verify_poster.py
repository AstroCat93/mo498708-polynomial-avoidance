"""Re-verify the poster's sharpness constructions (blocking families for degree <= d-1) for all primes p <= 61.

 d = 1    : A_i = {i}.                     Check: every constant c hits (i = c).
 d = 2    : A_i = {0, i} (i != 0), A_0 = {0, 1}.   Check all p^2 polynomials of degree <= 1.
 d = p-2  : B_i = F_p minus A_i = {g(i), g(i)+1}, deg g = p-2 (we use g = x^{p-2} and also random g of degree p-2).
            Check: #{F in prod B_i : sum_i F(i) = 0 and sum_i i F(i) = 0} = 0, by exact DP over F_p^2
            (these two moments vanish iff deg F <= p-3).
 d = p-1  : B_i = {g(i)}, deg g = p-1.  Avoider of degree <= p-2 exists iff sum_i g(i) = 0 iff coeff of x^{p-1} is 0.
Also cross-checks the moment characterisation  sum_x x^k F(x) = -c_{p-1-k}  on random polynomials.
"""
import itertools, random
from sympy import primerange

def evalp(c, x, p):
    r = 0
    for a in reversed(c):
        r = (r * x + a) % p
    return r

def moments_ok(p, trials=20):
    for _ in range(trials):
        c = [random.randrange(p) for _ in range(p)]
        for k in range(p - 1):
            if sum(pow(x, k, p) * evalp(c, x, p) for x in range(p)) % p != (-c[p - 1 - k]) % p:
                return False
    return True

def dp_count(p, B, K):
    """#{F in prod B_x : sum_x x^k F(x) = 0 for k < K}, exact DP over F_p^K (dict)."""
    cur = {(0,) * K: 1}
    for x in range(p):
        v = [pow(x, k, p) for k in range(K)]
        nxt = {}
        for s, n in cur.items():
            for b in B[x]:
                t = tuple((s[k] + b * v[k]) % p for k in range(K))
                nxt[t] = nxt.get(t, 0) + n
        cur = nxt
    return cur.get((0,) * K, 0)

random.seed(1)
allok = True
for p in primerange(2, 62):
    res = {}
    assert moments_ok(p)
    # d = 1
    A = [{i} for i in range(p)]
    res['d=1'] = all(any(c in A[i] for i in range(p)) for c in range(p))
    # d = 2
    if p >= 3:
        A = [{0, i} if i else {0, 1} for i in range(p)]
        res['d=2'] = all(any((a * i + b) % p in A[i] for i in range(p)) for a in range(p) for b in range(p))
    # d = p-2 (needs p-2 >= 1)
    if p >= 3:
        ok = True
        gs = [[0] * (p - 2) + [1]]  # x^{p-2}
        for _ in range(3):
            g = [random.randrange(p) for _ in range(p - 2)] + [random.randrange(1, p)]
            gs.append(g)
        for g in gs:
            B = [{evalp(g, i, p), (evalp(g, i, p) + 1) % p} for i in range(p)]
            if dp_count(p, B, 2) != 0: ok = False
        res['d=p-2'] = ok
    # d = p-1
    g = [random.randrange(p) for _ in range(p - 1)] + [random.randrange(1, p)]
    res['d=p-1'] = (sum(evalp(g, i, p) for i in range(p)) % p) != 0
    allok &= all(res.values())
    print(p, res)
print("ALL CONSTRUCTIONS VERIFIED" if allok else "FAILURE")
