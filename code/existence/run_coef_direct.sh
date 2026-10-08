#!/bin/bash
# Runs coef_direct on every line "p d mode seed" of coef_plan.txt (3 in parallel) and compares
# with the closed form (-1)^{d(d+1)/2} prod_k binom(d,k) mod p.  Output: $LOGDIR/coef_direct.txt
# (LOGDIR defaults to ../../logs, i.e. the committed logs are overwritten; set LOGDIR to keep them).
# Takes about 30 s on 3 cores (about 75 CPU-seconds).  Set CC to override the compiler.
cd "$(dirname "$0")"
${CC:-clang} -O3 -o coef_direct coef_direct.c || exit 1
export LOGDIR=${LOGDIR:-../../logs}
mkdir -p "$LOGDIR"
tr '\n' '\0' < coef_plan.txt | xargs -0 -P 3 -I{} sh -c './coef_direct {}' > "$LOGDIR/coef_direct_raw.txt"
python3 - <<'PY'
import os
from math import comb, prod
L=os.environ['LOGDIR']
bad=0; n=0; modes={0:0,1:0,2:0}
for line in open(L+'/coef_direct_raw.txt'):
    p,d,mode,c=map(int,line.split())
    cf=((-1)**(d*(d+1)//2)*prod(comb(d,k) for k in range(d+1)))%p
    n+=1; modes[mode]+=1
    if c!=cf: bad+=1; print('MISMATCH',p,d,mode,c,cf)
out='coef_direct: %d runs (mode0 random families=%d, mode1 top part=%d, mode2 reduced=%d), mismatches vs closed form: %d'%(n,modes[0],modes[1],modes[2],bad)
print(out); open(L+'/coef_direct.txt','w').write(open(L+'/coef_direct_raw.txt').read()+out+'\n')
PY
