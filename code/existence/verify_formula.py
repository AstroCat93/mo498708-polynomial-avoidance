# Verify: A_k(d) := sum_{F monic, deg k} N(F)^d (mod p), N(F)=prod_{i in F_p^*} F(i),
# equals [u^k] prod_{t=1}^d (1 - gamma_t u), gamma_t = (-1)^(d-t) binom(d,t), for k < p.
# In particular C(d) = A_d(d) = (-1)^{d(d+1)/2} prod_t binom(d,t).
import numpy as np, sys
from math import comb, prod
def Ak_all(p,k):
    n=p**k; idx=np.arange(n,dtype=np.int64)
    cs=[(idx//p**j)%p for j in range(k)]
    N=np.ones(n,dtype=np.int64)
    for i in range(1,p):
        v=np.full(n,pow(i,k,p),dtype=np.int64)
        for j in range(k): v=(v+cs[j]*pow(i,j,p))%p
        N=(N*v)%p
    out=[]; Nd=np.ones(n,dtype=np.int64)
    for d in range(p):
        out.append(int(Nd.sum()%p)); Nd=(Nd*N)%p
    return out  # index d
def predicted(p,d,k):
    poly=[1]
    for t in range(1,d+1):
        g=((-1)**(d-t)*comb(d,t))%p
        new=[0]*(len(poly)+1)
        for a,c in enumerate(poly):
            new[a]=(new[a]+c)%p; new[a+1]=(new[a+1]-g*c)%p
        poly=new
    return poly[k] if k<len(poly) else 0
bad=0; checked=0
for p in [2,3,5,7,11,13,17,19,23]:
    for k in range(0,p):
        if p**k>3_000_000: break
        A=Ak_all(p,k)
        for d in range(0,p):
            pr=predicted(p,d,k)
            checked+=1
            if A[d]!=pr:
                bad+=1; print('MISMATCH',p,k,d,A[d],pr)
    # closed form for C(d)=A_d(d)
print('checked',checked,'mismatches',bad)
# explicit C(d) table from closed form vs brute A_d(d)
for p in [5,7,11,13,17,19,23,29,31]:
    row=[]
    for d in range(0,p):
        if p**d>3_000_000: break
        A=Ak_all(p,d)[d]
        cf=((-1)**(d*(d+1)//2)*prod(comb(d,t) for t in range(d+1)))%p
        row.append((d,A,cf,A==cf))
    print(p,all(r[3] for r in row),[(r[0],r[1]) for r in row])
