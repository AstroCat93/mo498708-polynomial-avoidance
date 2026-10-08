# End-to-end sanity test of the (11,8) theorem on many families (random and structured):
# for each family A_i (|A_i|=8) find explicitly f with deg f <= 7 and f(i) notin A_i, and verify f directly.
import random, itertools
p,d=11,8; k=p-d
def find_poly(C):
    # DP over moment vectors (sum_i y_i i^j)_{j<3} with back-pointers; returns y or None
    states={(0,0,0):None}; layers=[]
    for i in range(p):
        v=(1,i%p,(i*i)%p); new={}
        for s in states:
            for c in C[i]:
                t=tuple((s[j]+c*v[j])%p for j in range(3))
                if t not in new: new[t]=(s,c)
        layers.append(new); states=new
    if (0,0,0) not in states: return None
    y=[None]*p; s=(0,0,0)
    for i in range(p-1,-1,-1):
        prev,c=layers[i][s]; y[i]=c; s=prev
    return y
def interp_deg(y):
    # degree of interpolating polynomial via coefficients a_m = -sum_i y_i i^{p-1-m} (m>=1), a_0 = y_0
    coeffs=[y[0]]+[(-sum(y[i]*pow(i,p-1-m,p) for i in range(p)))%p for m in range(1,p)]
    deg=max([m for m in range(p) if coeffs[m]%p],default=0)
    # evaluate to double-check
    for i in range(p): assert sum(coeffs[m]*pow(i,m,p) for m in range(p))%p==y[i]
    return deg
rng=random.Random(1)
fams=[]
for _ in range(3000): fams.append([rng.sample(range(p),3) for i in range(p)])
for _ in range(500):
    g=[rng.randrange(p) for i in range(p)]; dlt=[rng.randrange(1,p) for i in range(p)]
    fams.append([[(g[i]+e*dlt[i])%p for e in (0,1,2)] for i in range(p)])   # APs
    fams.append([[(g[i]+e)%p for e in (0,1,2)] for i in range(p)])            # unit APs
    fams.append([[(g[i]+e)%p for e in (0,1,p-1)] for i in range(p)])
D=[[0,1,10]]+[[0,9,10]]*7
for c8 in itertools.combinations(range(p),3):
    fams.append(D+[list(c8),[0,1,2],[3,5,7]])
bad=0; maxdeg=0
for C in fams:
    y=find_poly(C)
    if y is None: bad+=1; print('NO SOLUTION',C); continue
    assert all(y[i] in C[i] for i in range(p))
    dg=interp_deg(y); maxdeg=max(maxdeg,dg); assert dg<=d-1
print('families tested',len(fams),'without solution',bad,'max degree of found f',maxdeg)
