# For random families (A_i), check  sum_{f: deg<=d} f(0)^{p-1-d} prod_i prod_{a in A_i} (f(i)-a) == (-1)^{d+1} C (mod p),
# with C = (-1)^{d(d+1)/2} prod_k binom(d,k); also report #avoiding f (must be >0).
import numpy as np, random
from math import comb, prod
random.seed(1)
def check(p, d, trials):
    n = p**(d+1)
    idx = np.arange(n, dtype=np.int64)
    cs = [(idx // p**j) % p for j in range(d+1)]
    vals = []
    for i in range(p):
        v = np.zeros(n, dtype=np.int64)
        for j in range(d+1):
            v = (v + cs[j]*pow(i, j, p)) % p
        vals.append(v)
    C = ((-1)**(d*(d+1)//2) * prod(comb(d,k) for k in range(d+1))) % p
    target = ((-1)**(d+1) * C) % p
    for t in range(trials):
        A = [random.sample(range(p), d) for _ in range(p)]
        P = np.ones(n, dtype=np.int64)
        for i in range(p):
            for a in A[i]:
                P = (P * ((vals[i] - a) % p)) % p
        w = np.ones(n, dtype=np.int64)
        for _ in range(p-1-d):
            w = (w * cs[0]) % p
        s = int((w*P % p).sum() % p)
        navoid = int((P != 0).sum())
        if s != target or navoid == 0:
            print("FAIL", p, d, A, s, target, navoid); return False
    print(p, d, "ok", trials, "trials; target", target, flush=True)
    return True
ok = True
for p, d, tr in [(5,1,50),(5,2,50),(5,3,50),(5,4,50),(7,2,40),(7,3,40),(7,4,30),(7,5,20),(11,2,20),(11,3,10),(11,4,5)]:
    ok &= check(p, d, tr)
print("ALL OK" if ok else "FAIL")
