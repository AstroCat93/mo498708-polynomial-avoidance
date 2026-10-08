# Verify s_n := sum_{beta in F_{p^n}} Norm_{F_{p^n}/F_p}(beta^{p-1}-1)^d  ==  -sum_{t=1}^d gamma_t^n,
# gamma_t = (-1)^{d-t} binom(d,t)  (mod p).  Also verify s_n = sum_{k|n} k sum_{pi monic irr deg k} N(pi)^{d n/k}.
import itertools, sympy as sp
from math import comb
def field(p,n):
    x=sp.symbols('x')
    # find monic irreducible of degree n
    for c in itertools.product(range(p),repeat=n):
        f=sp.Poly([1]+list(c),x,modulus=p)
        if f.is_irreducible: return f
def mulmod(a,b,mod,p):
    n=len(mod)-1
    r=[0]*(2*n-1)
    for i,x in enumerate(a):
        if x:
            for j,y in enumerate(b): r[i+j]=(r[i+j]+x*y)%p
    # reduce: mod is monic list high->low; elements are low->high lists of length n
    m=[c for c in reversed(mod)]  # low->high, m[n]=1
    for k in range(2*n-2,n-1,-1):
        c=r[k]
        if c:
            for j in range(n+1): r[k-n+j]=(r[k-n+j]-c*m[j])%p
    return r[:n]
def powmod(a,e,mod,p):
    n=len(mod)-1
    res=[1]+[0]*(n-1); b=a[:]
    while e:
        if e&1: res=mulmod(res,b,mod,p)
        b=mulmod(b,b,mod,p); e>>=1
    return res
for p in [3,5,7]:
    for n in [1,2,3]:
        if p**n>400: continue
        f=field(p,n); mod=[int(c)%p for c in f.all_coeffs()]
        R=(p**n-1)//(p-1)
        # norm(y)=y^R lies in F_p
        vals=[]
        for beta in itertools.product(range(p),repeat=n):
            b=list(beta)
            y=powmod(b,p-1,mod,p); y[0]=(y[0]-1)%p
            nm=powmod(y,R,mod,p)
            assert all(v==0 for v in nm[1:]), 'norm not in F_p'
            vals.append(nm[0])
        for d in range(1,p):
            s=sum(pow(v,d,p) for v in vals)%p
            pred=(-sum(pow(((-1)**(d-t)*comb(d,t))%p,n,p) for t in range(1,d+1)))%p
            print(p,n,d,s,pred,'OK' if s==pred else 'BAD')
