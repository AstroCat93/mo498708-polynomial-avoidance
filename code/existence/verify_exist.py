# Sanity: (a) exhaustive over all families for p in {2,3,5}; (b) adversarial local search for p=7,11.
import numpy as np, itertools, random
def table(p,d):
    coeffs=np.array(list(itertools.product(range(p),repeat=d+1)))
    pw=np.array([[pow(i,j,p) for i in range(p)] for j in range(d+1)])
    return (coeffs@pw)%p   # (#polys) x p
def min_avoiders_exhaustive(p,d):
    V=table(p,d); subsets=list(itertools.combinations(range(p),d))
    # mask[s][a]=a in subset s
    mask=np.zeros((len(subsets),p),dtype=bool)
    for s,S in enumerate(subsets): mask[s,list(S)]=True
    best=None
    # iterate over families via product; vectorize over last coordinate
    for fam in itertools.product(range(len(subsets)),repeat=p-1):
        hit=np.zeros(V.shape[0],dtype=bool)
        for i,s in enumerate(fam): hit|=mask[s][V[:,i]]
        # last point: all choices
        last=mask[:,V[:,p-1]]   # (#subsets, #polys)
        cnt=(~(hit[None,:]|last)).sum(axis=1).min()
        best=cnt if best is None else min(best,cnt)
    return int(best)
for p in [2,3,5]:
    for d in range(0,p):
        print('exhaustive p=%d d=%d min #avoiders over all families ='%(p,d),min_avoiders_exhaustive(p,d),flush=True)
def adversarial(p,d,restarts=20,steps=3000,seed=7):
    rng=random.Random(seed); V=table(p,d); best=None
    for r in range(restarts):
        M=np.zeros((p,p),dtype=bool)
        for i in range(p): M[i,rng.sample(range(p),d)]=True
        def cnt(M): return int((~M[np.arange(p)[None,:],V].any(axis=1)).sum())
        cur=cnt(M)
        for s in range(steps):
            i=rng.randrange(p); ins=np.nonzero(M[i])[0]; outs=np.nonzero(~M[i])[0]
            if len(ins)==0 or len(outs)==0: break
            a=rng.choice(list(ins)); b=rng.choice(list(outs))
            M[i,a]=False; M[i,b]=True; new=cnt(M)
            if new<=cur or rng.random()<0.01: cur=new
            else: M[i,b]=False; M[i,a]=True
        best=cur if best is None else min(best,cur)
    return best
for p,d in [(7,2),(7,3),(7,4),(7,5),(11,2),(11,3),(11,4)]:
    print('adversarial p=%d d=%d min #avoiders found ='%(p,d),adversarial(p,d),flush=True)
