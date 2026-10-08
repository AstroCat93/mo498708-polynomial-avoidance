# Verify every FOUND line printed by `indep_k3 7` is a genuine blocking family for (p,d)=(7,4):
# A_i = F_7 \ C_i (|A_i| = 4) and EVERY f with deg f <= 3 has f(i) in A_i for some i (all 7^4 polynomials).
import sys, re, itertools
p, d = 7, 4
polys = [[sum(c[j]*pow(i, j, p) for j in range(d)) % p for i in range(p)] for c in itertools.product(range(p), repeat=d)]
n = bad = 0
for line in sys.stdin:
    if not line.startswith('FOUND'): continue
    C = {}
    for i, s in re.findall(r'C_(\d+)=\{([\d,]+)\}', line):
        C[int(i)] = set(map(int, s.split(',')))
    assert sorted(C) == list(range(p)) and all(len(v) == 3 for v in C.values())
    A = [set(range(p)) - C[i] for i in range(p)]
    blocked = all(any(f[i] in A[i] for i in range(p)) for f in polys)
    n += 1; bad += (not blocked)
print('found families checked:', n, ' not actually blocking:', bad)
