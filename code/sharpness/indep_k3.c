/* indep_k3.c -- independent re-implementation (written 2026-10-08 for the final write-up, without
 * reusing dualk3c/dualk3d) of the exhaustive search deciding whether a blocking family exists
 * for degree <= d-1 when d = p-3.
 *
 * Reformulation (proved in solution.md, Lemma 3.1):  with C_i = F_p \ A_i (|C_i| = 3) and
 * v_i = (1, i, i^2) in F_p^3 (0^0 = 1), the family (A_i) blocks every f with deg f <= p-4
 *   <=>  0 is NOT in the sumset  sum_{i in F_p} C_i v_i.
 *
 * Normalisation (proved in solution.md, Lemma 3.3, normalisation N1) -- different from the one in dualk3c/d:
 *   W = {0,1,...,p-4}, Z = {p-3,p-2,p-1}  (or Z given on the command line, W = complement, 0 in W)
 *   C_0 = {0,1,u} where u is the least element of its orbit under the anharmonic group
 *         u -> {u, 1-u, 1/u, 1/(1-u), u/(u-1), (u-1)/u}
 *   C_w (w in W, w != 0) = {0,a,b}, the lexicographically least of its 3 translates containing 0
 *   C_z (z in Z) arbitrary 3-subsets  (no restriction at all).
 * No AGL-type ordering and no domain symmetry is used.
 *
 * For each pair (u, box (C_z)_{z in Z}) we decide by DFS whether some choice of the C_w
 * (w in W\{0}) makes S_W := sum_{w in W} C_w v_w disjoint from T := -sum_{z in Z} C_z v_z.
 * Because 0 lies in every C_w (w != 0), partial sums only grow, so a partial S meeting T is dead.
 *
 * usage:  indep_k3 p [start step [z1 z2 z3]]      -- DFS mode, prints summary (and any FOUND family)
 *         indep_k3 p brute                         -- (small p only) for every box compares DFS with
 *                                                     a pruning-free enumeration of all W-assignments
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define MP 13
static int p, P3;
static int Zc[3], Wc[MP], nW;
static int vec[MP][3];
static int canon[MP*MP][2], ncanon;      /* canonical {0,a,b} */
static int urep[MP], nurep;
static int subs[1000][3], nsubs;
static unsigned char Tmark[MP*MP*MP];    /* marks points of T */
static long long nodes;
static int choice[MP];

static inline int enc(int a,int b,int c){ return a + p*(b + p*c); }
static inline int addv(int s,int u,int w){ /* s + u*v_w */
  int a=s%p, b=(s/p)%p, c=s/(p*p);
  a=(a+u*vec[w][0])%p; b=(b+u*vec[w][1])%p; c=(c+u*vec[w][2])%p; return enc(a,b,c); }
static int inv(int x){ for(int y=1;y<p;y++) if(x*y%p==1) return y; return -1; }

/* S is given as point list pts[0..n) plus membership array mem */
typedef struct { int n; int pts[MP*MP*MP]; unsigned char mem[MP*MP*MP]; } Set;

static int Tlist[27];
static int ok_shift(const Set*S,int u,int w){ /* (S + u v_w) disjoint from T  <=>  S disjoint from T - u v_w */
  for(int k=0;k<27;k++) if(S->mem[addv(Tlist[k],(p-u)%p,w)]) return 0; return 1; }

static int dfs(const Set*S, unsigned used){
  nodes++;
  /* choose the unassigned W column (w != 0) with fewest viable canonical sets */
  int bestj=-1,bestc=1<<30; static unsigned char okc[64][MP*MP];
  unsigned char okj[MP][MP];
  for(int j=1;j<nW;j++){ if(used>>j&1) continue; int w=Wc[j];
    for(int u=1;u<p;u++) okj[j][u]=ok_shift(S,u,w);
    int c=0; for(int q=0;q<ncanon;q++) if(okj[j][canon[q][0]]&&okj[j][canon[q][1]]) c++;
    if(c==0) return 0;
    if(c<bestc){bestc=c;bestj=j;} }
  if(bestj<0) return 1;
  int w=Wc[bestj];
  Set *S2=malloc(sizeof(Set));
  for(int q=0;q<ncanon;q++){ int a=canon[q][0],b=canon[q][1];
    if(!(okj[bestj][a]&&okj[bestj][b])) continue;
    memcpy(S2,S,sizeof(Set));
    for(int k=0;k<S->n;k++){ int x=addv(S->pts[k],a,w); if(!S2->mem[x]){S2->mem[x]=1;S2->pts[S2->n++]=x;}
                             x=addv(S->pts[k],b,w); if(!S2->mem[x]){S2->mem[x]=1;S2->pts[S2->n++]=x;} }
    choice[bestj]=q;
    if(dfs(S2,used|(1u<<bestj))){ free(S2); return 1; } }
  free(S2); (void)okc; return 0; }

static void build_T(int bz[3]){
  memset(Tmark,0,P3);
  for(int x=0;x<3;x++)for(int y=0;y<3;y++)for(int z=0;z<3;z++){
    int s=enc(0,0,0); s=addv(s,subs[bz[0]][x],Zc[0]); s=addv(s,subs[bz[1]][y],Zc[1]); s=addv(s,subs[bz[2]][z],Zc[2]);
    int a=s%p,b=(s/p)%p,c=s/(p*p); int t=enc((p-a)%p,(p-b)%p,(p-c)%p); Tmark[t]=1; Tlist[9*x+3*y+z]=t; } }

static int box_dfs(int u,int bz[3]){
  build_T(bz);
  Set *S=calloc(1,sizeof(Set));
  int c0[3]={0,1,u};
  for(int x=0;x<3;x++){ int s=addv(enc(0,0,0),c0[x],0); if(Tmark[s]){free(S);return 0;} if(!S->mem[s]){S->mem[s]=1;S->pts[S->n++]=s;} }
  int r=dfs(S,1u); free(S); return r; }

int main(int argc,char**argv){
  p=atoi(argv[1]); P3=p*p*p; if(p>MP||p<5){fprintf(stderr,"p range\n");return 1;}
  int brute = (argc>2 && strcmp(argv[2],"brute")==0);
  long long start=0,step=1; if(!brute && argc>3){start=atoll(argv[2]);step=atoll(argv[3]);}
  Zc[0]=p-3;Zc[1]=p-2;Zc[2]=p-1;
  if(!brute && argc>6){Zc[0]=atoi(argv[4]);Zc[1]=atoi(argv[5]);Zc[2]=atoi(argv[6]);}
  nW=0; Wc[nW++]=0; for(int i=1;i<p;i++) if(i!=Zc[0]&&i!=Zc[1]&&i!=Zc[2]) Wc[nW++]=i;
  if(nW!=p-3){fprintf(stderr,"bad Z (must be 3 distinct nonzero columns)\n");return 1;}
  for(int i=0;i<p;i++){ vec[i][0]=1; vec[i][1]=i; vec[i][2]=i*i%p; }
  /* canonical translates {0,a,b}, 0<a<b: lex-least among {0,a,b}, {-a,0,b-a}, {-b,a-b,0} (each sorted) */
  ncanon=0;
  for(int a=1;a<p;a++)for(int b=a+1;b<p;b++){
    int t1[2]={(p-a)%p,(b-a)%p}, t2[2]={(p-b)%p,(a-b+p)%p};
    if(t1[0]>t1[1]){int t=t1[0];t1[0]=t1[1];t1[1]=t;} if(t2[0]>t2[1]){int t=t2[0];t2[0]=t2[1];t2[1]=t;}
    int k=a*p+b, k1=t1[0]*p+t1[1], k2=t2[0]*p+t2[1];
    if(k<=k1 && k<=k2){canon[ncanon][0]=a;canon[ncanon][1]=b;ncanon++;} }
  /* anharmonic orbit representatives u in {2..p-1} */
  nurep=0;
  for(int u=2;u<p;u++){ int iu=inv(u), i1u=inv((1-u+p)%p), ium1=inv((u-1)%p);
    int orb[6]={u,(1-u+p)%p,iu,i1u,u*ium1%p,(u-1)*iu%p}; int m=p;
    for(int q=0;q<6;q++) if(orb[q]<m) m=orb[q];
    if(m==u) urep[nurep++]=u; }
  nsubs=0; for(int a=0;a<p;a++)for(int b=a+1;b<p;b++)for(int c=b+1;c<p;c++){subs[nsubs][0]=a;subs[nsubs][1]=b;subs[nsubs][2]=c;nsubs++;}
  fprintf(stderr,"p=%d Z={%d,%d,%d} canonical W-sets=%d u-reps=",p,Zc[0],Zc[1],Zc[2],ncanon);
  for(int q=0;q<nurep;q++) fprintf(stderr,"%d ",urep[q]);
  long long nbox=(long long)nurep*nsubs*nsubs*nsubs;
  fprintf(stderr," subsets=%d total (u,box)=%lld\n",nsubs,nbox);

  if(!brute){
    long long checked=0,found=0; nodes=0;
    for(long long bi=start;bi<nbox;bi+=step){
      long long r=bi; int bz[3]; bz[2]=r%nsubs; r/=nsubs; bz[1]=r%nsubs; r/=nsubs; bz[0]=r%nsubs; r/=nsubs; int u=urep[r];
      checked++;
      if(box_dfs(u,bz)){ found++;
        printf("FOUND C_0={0,1,%d}",u);
        for(int j=1;j<nW;j++) printf(" C_%d={0,%d,%d}",Wc[j],canon[choice[j]][0],canon[choice[j]][1]);
        for(int q=0;q<3;q++) printf(" C_%d={%d,%d,%d}",Zc[q],subs[bz[q]][0],subs[bz[q]][1],subs[bz[q]][2]);
        printf("\n"); fflush(stdout); }
    }
    printf("DONE p=%d Z={%d,%d,%d} start=%lld step=%lld checked=%lld nodes=%lld found=%lld\n",p,Zc[0],Zc[1],Zc[2],start,step,checked,nodes,found);
    return 0;
  }
  /* brute mode: enumerate ALL W-assignments, store their full sumsets S_W as bitmaps */
  long long nas=nurep; for(int j=1;j<nW;j++) nas*=ncanon;
  if(nas>2000000){fprintf(stderr,"too many W-assignments for brute mode\n");return 1;}
  unsigned char *SW=malloc((size_t)nas*P3);
  for(long long a=0;a<nas;a++){
    long long r=a; int cj[MP]; for(int j=nW-1;j>=1;j--){cj[j]=r%ncanon; r/=ncanon;} int u=urep[r];
    unsigned char *cur=calloc(P3,1), *nx=malloc(P3);
    cur[0]=1;
    for(int j=0;j<nW;j++){ int set[3]; if(j==0){set[0]=0;set[1]=1;set[2]=u;} else {set[0]=0;set[1]=canon[cj[j]][0];set[2]=canon[cj[j]][1];}
      memset(nx,0,P3);
      for(int s=0;s<P3;s++) if(cur[s]) for(int e=0;e<3;e++) nx[addv(s,set[e],Wc[j])]=1;
      memcpy(cur,nx,P3); }
    memcpy(SW+(size_t)a*P3,cur,P3); free(cur); free(nx); }
  long long mism=0, pos=0, nb=0;
  for(int b0=0;b0<nsubs;b0++)for(int b1=0;b1<nsubs;b1++)for(int b2=0;b2<nsubs;b2++){
    int bz[3]={b0,b1,b2}; build_T(bz);
    for(int q=0;q<nurep;q++){
      int bru=0;
      long long per=nas/nurep;  /* assignments with u=urep[q] occupy indices [q*per,(q+1)*per) */
      for(long long a=q*per; a<(q+1)*per && !bru; a++){
        unsigned char *S=SW+(size_t)a*P3; int hit=0;
        for(int s=0;s<P3 && !hit;s++) if(S[s]&&Tmark[s]) hit=1;
        if(!hit) bru=1; }
      int df=box_dfs(urep[q],bz);
      nb++; if(bru) pos++; if(bru!=df){ mism++; if(mism<10) printf("MISMATCH u=%d box=%d,%d,%d brute=%d dfs=%d\n",urep[q],b0,b1,b2,bru,df);} } }
  printf("BRUTE p=%d (u,box) pairs=%lld with completion=%lld mismatches(dfs vs brute)=%lld\n",p,nb,pos,mism);
  return 0; }
