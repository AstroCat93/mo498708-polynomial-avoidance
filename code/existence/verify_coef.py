# Direct check: coefficient of c_0^d prod_{j>=1} c_j^{p-1} in prod_{i in F_p} f(i)^d vs closed form.
import sys
from collections import defaultdict
from math import comb, prod
def mul(A,B,p):
    C=defaultdict(int)
    for a,x in A.items():
        for b,y in B.items():
            C[tuple(u+v for u,v in zip(a,b))]=(C[tuple(u+v for u,v in zip(a,b))]+x*y)%p
    return {k:v for k,v in C.items() if v}
def coef(p,d):
    nv=d+1
    N={tuple([0]*nv):1}
    for i in range(p):
        lin={}
        for j in range(nv):
            e=[0]*nv; e[j]=1
            co=1 if (i==0 and j==0) else pow(i,j,p)
            if co%p: lin[tuple(e)]=co%p
        N=mul(N,lin,p)
    # prune monomials with exponent > p-1 only at the end (cannot prune early: none exceed since we need exact)
    P={tuple([0]*nv):1}
    for _ in range(d):
        P=mul(P,N,p)
        P={k:v for k,v in P.items() if max(k)<=p-1}  # safe: exponents only grow
    return P.get(tuple([d]+[p-1]*d),0), sorted(k for k in P if sum(k)==p*d)
for p,d in [(5,4),(7,5),(7,6),(13,2),(13,3),(11,4)]:
    c,mons=coef(p,d)
    cf=((-1)**(d*(d+1)//2)*prod(comb(d,t) for t in range(d+1)))%p
    print(p,d,'coef',c,'closed',cf,'admissible monomials',mons,flush=True)
