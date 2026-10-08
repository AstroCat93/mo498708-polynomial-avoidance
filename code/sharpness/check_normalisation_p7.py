# check_normalisation_p7.py -- tests that normalisation N1 (solution.md, Lemma 3.3) is complete at p=7, d=4.
# Takes the explicit blocking family of Proposition 4 (d=4) and 200 random images of it under the maps of
# Lemma 3.2 (a),(b); normalises each one as in Lemma 3.3 and checks that every resulting (C_0, Z-box) is among
# the blocking families found by the DFS.  Written by an independent reviewer (a separate Claude instance).
# usage (in code/sharpness/):  ./indep_k3 7 > found7.txt && python3 check_normalisation_p7.py found7.txt
import itertools,re,random,sys
p=7; Z=[4,5,6]; Wl=[0,1,2,3]
found=set()
for line in open(sys.argv[1]):
    if not line.startswith('FOUND'): continue
    sets=dict((int(a),tuple(sorted(map(int,b.split(','))))) for a,b in re.findall(r'C_(\d+)=\{([\d,]+)\}',line))
    found.add((sets[0],sets[4],sets[5],sets[6]))
inv=lambda x: pow(x,p-2,p)
def orbit(u): return {u,(1-u)%p,inv(u),inv((1-u)%p),u*inv((u-1)%p)%p,(u-1)*inv(u)%p}
def canon(S):
    best=None
    for x in S:
        T=tuple(sorted((s-x)%p for s in S))
        if best is None or T<best: best=T
    return best
def lagr(vals):  # vals dict w->value, eval at z
    def ev(z):
        s=0
        for w,v in vals.items():
            num=1;den=1
            for w2 in vals:
                if w2!=w: num=num*(z-w2)%p; den=den*(w-w2)%p
            s=(s+v*num*inv(den))%p
        return s
    return ev
def normalised_boxes(C):
    out=set()
    for a,b,c in itertools.permutations(C[0]):
        lam=inv((b-a)%p); u=(c-a)*lam%p
        if u!=min(orbit(u)): continue
        vals={0:(-lam*a)%p}
        for w in Wl[1:]:
            LC=[lam*s%p for s in C[w]]
            ct=canon(LC)
            xs=[x for x in LC if tuple(sorted((s-x)%p for s in LC))==ct]
            vals[w]=(-xs[0])%p
        h=lagr(vals)
        new0=tuple(sorted((lam*s+vals[0])%p for s in C[0]))
        box=tuple(tuple(sorted((lam*s+h(z))%p for s in C[z])) for z in Z)
        out.add((new0,)+box)
    return out
def blocks(C):
    for co in itertools.product(range(p),repeat=4):
        if all(sum(co[j]*i**j for j in range(4))%p in C[i] for i in range(p)): return False
    return True
A4=[{0,1,2,4}]+[{(pow(i,4,7)*x)%7 for x in (0,1,2,6)} for i in range(1,7)]
C=[sorted(set(range(7))-a) for a in A4]
nb=normalised_boxes(C); print("explicit family blocks:",blocks(C),"normalised boxes:",nb,"in found:",[b in found for b in nb])
# random transforms of explicit family (3.2(a),(b)) -> blocking families, check normalisation lands in found
random.seed(1); ok=0;tot=0
for trial in range(200):
    al=random.randrange(1,p);be=random.randrange(p);lam=random.randrange(1,p);hc=[random.randrange(p) for _ in range(4)]
    C2=[sorted({(lam*s+sum(hc[j]*i**j for j in range(4)))%p for s in C[(al*i+be)%p]}) for i in range(p)]
    nb=normalised_boxes(C2); tot+=1; ok+= all(b in found for b in nb) and len(nb)>0
print("random transformed families:",tot,"all normalised boxes found:",ok)
