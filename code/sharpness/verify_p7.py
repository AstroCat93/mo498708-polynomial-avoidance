# Explicit structured blocking families for p=7, d=3 and d=4 (brute-force verified).
import itertools
def brute_check(p,d,A):
    S=[set(a) for a in A]
    bad=[c for c in itertools.product(range(p),repeat=d)
         if not any(sum(c[j]*pow(i,j,p) for j in range(d))%p in S[i] for i in range(p))]
    return len(bad)==0
p=7
chi=lambda i: pow(i,3,p)  # quadratic character mod 7 (as 1 or 6)
A3=[[0,1,6]]+[sorted((chi(i)*a)%p for a in (1,2,3)) for i in range(1,p)]
A4=[[0,1,2,4]]+[sorted((pow(i,4,p)*a)%p for a in (0,1,2,6)) for i in range(1,p)]
print('d=3 family A_i = chi(i)*{1,2,3}, A_0={0,1,6}:',A3,brute_check(p,3,A3))
print('d=4 family A_i = i^4*{0,1,2,6}, A_0={0,1,2,4}:',A4,brute_check(p,4,A4))
