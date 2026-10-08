/* Direct (definition-level) computation of the Combinatorial-Nullstellensatz coefficient
 *
 *   C(p,d) = [ c_0^d * prod_{j=1}^d c_j^{p-1} ]  P(c),
 *   P(c)   = prod_{i in F_p} prod_{a in A_i} ( f_c(i) - a ),   f_c(x) = sum_{j=0}^d c_j x^j,
 *
 * by dense truncated polynomial expansion over F_p.  Exponent vectors are truncated at
 * e_0 <= d, e_j <= p-1 (j>=1): multiplication by linear (possibly inhomogeneous) forms never
 * lowers exponents, so truncated monomials can never contribute to the target monomial.
 *
 * usage: coef_direct p d mode [seed]
 *   mode 0 : "full", A_i = random d-subsets of F_p (seeded), all d+1 variables
 *   mode 1 : "full", A_i = {0,...,0}  (i.e. top homogeneous part prod_i f_c(i)^d), d+1 variables
 *   mode 2 : "reduced": C = [prod_{j>=1} c_j^{p-1}] prod_{i != 0} (sum_{j>=1} c_j i^j)^d
 *            (valid because the i=0 factor is c_0^d and every other factor needs c_0-degree 0)
 * prints: p d mode C
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

static uint64_t rng_state = 88172645463325252ULL;
static uint64_t xs(void){ rng_state ^= rng_state<<13; rng_state ^= rng_state>>7; rng_state ^= rng_state<<17; return rng_state; }

int main(int argc, char **argv){
    if(argc<4){fprintf(stderr,"usage\n");return 1;}
    int p=atoi(argv[1]), d=atoi(argv[2]), mode=atoi(argv[3]);
    if(argc>4) rng_state ^= (uint64_t)atoll(argv[4])*0x9E3779B97F4A7C15ULL;
    if(d==0){ printf("%d %d %d %d\n",p,d,mode,1); return 0; } /* empty product: P=1, target monomial 1 */
    int full = (mode!=2);
    int nv = full ? d+1 : d;           /* number of variables */
    /* radix per variable */
    long long rad[64], stride[64]; long long size=1;
    for(int v=0; v<nv; v++){
        int j = full ? v : v+1;        /* actual coefficient index c_j */
        rad[v] = (full && j==0) ? d+1 : p;   /* e_0 <= d, e_j <= p-1 */
        stride[v]=size; size*=rad[v];
    }
    uint8_t *A = calloc(size,1);
    if(!A){fprintf(stderr,"oom\n");return 1;}
    A[0]=1;
    int *ev = malloc(sizeof(int)*nv);
    for(int i=0;i<p;i++){
        if(!full && i==0) continue;
        /* linear form coefficients a_v = i^j (0^0 = 1) */
        int coef[64];
        for(int v=0; v<nv; v++){
            int j = full ? v : v+1; long long t=1;
            for(int k=0;k<j;k++) t=t*i%p;
            coef[v]=(int)t;
        }
        /* the d constants a in A_i */
        int consts[64];
        if(mode==0){ /* random d-subset */
            int perm[256]; for(int a=0;a<p;a++) perm[a]=a;
            for(int a=p-1;a>0;a--){int r=xs()%(a+1); int t=perm[a]; perm[a]=perm[r]; perm[r]=t;}
            for(int k=0;k<d;k++) consts[k]=perm[k];
        } else for(int k=0;k<d;k++) consts[k]=0;
        for(int k=0;k<d;k++){
            int a = consts[k];
            int nega = (p - a)%p;
            /* in place multiply by (L_i - a), descending index order */
            /* iterate indices descending, maintain exponent vector */
            for(int v=0; v<nv; v++) ev[v]=rad[v]-1;
            for(long long idx=size-1; idx>=0; idx--){
                long long acc = (long long)nega * A[idx];
                for(int v=0; v<nv; v++) if(ev[v]>0 && coef[v]) acc += (long long)coef[v]*A[idx-stride[v]];
                A[idx] = (uint8_t)(acc % p);
                /* decrement exponent vector */
                for(int v=0; v<nv; v++){ if(ev[v]>0){ev[v]--; break;} ev[v]=rad[v]-1; }
            }
        }
    }
    long long tgt=0;
    for(int v=0; v<nv; v++) tgt += (long long)(rad[v]-1)*stride[v];
    printf("%d %d %d %d\n",p,d,mode,A[tgt]);
    return 0;
}
