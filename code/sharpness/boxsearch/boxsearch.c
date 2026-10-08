/* boxsearch.c -- third, independent exhaustive search for k=3 (d=p-3) blocking families.
 *
 * Provenance: written from scratch by an independent verifier (a separate Claude instance) that did not
 * reuse dualk3c/dualk3d/indep_k3.  It uses the "box formulation" of solution.md, Remark 3.5, which needs
 * only Lemma 3.1 and global scaling -- not the normalisations N1/N2 (Lemmas 3.3/3.4) or any Z-symmetry.
 *
 * Formulation:
 *   family C_i (3-sets), v_i=(1,i,i^2). Blocking for deg<=d-1  <=>  0 notin sum_i C_i v_i.
 *   Fix Z={z1,z2,z3} (distinct), W = F_p \ Z.  Write C_w = D_w + t_w, D_w a fixed
 *   0-containing representative of the translation class of C_w.  Then
 *     sum_i C_i v_i = S_W + (sum_w t_w v_w) + sum_z C_z v_z,  S_W = sum_w D_w v_w.
 *   In coordinates w.r.t. basis (v_z1,v_z2,v_z3), sum_z C_z v_z = C_z1 x C_z2 x C_z3 (a box),
 *   and a translate of a box is a box.  So a blocking family exists
 *     <=> some assignment of classes D_w has complement(S_W) containing (minus) a box
 *     <=> complement(S_W) contains a combinatorial box A1xA2xA3, |Aj|=3.
 *   Global scaling lambda maps the problem to itself, so D_{w0} (first W column) can be
 *   restricted to one rep per scaling orbit of classes  (optional: flag noscale).
 *   S grows when columns are added (0 in D_w) so complement shrinks: prune when no box.
 *
 * usage: boxsearch p z1 z2 z3 [chunk nchunks] [noscale] [boxdepth]      (5 <= p <= 13)
 *   chunk/nchunks : split the work into nchunks interleaved parts and run part `chunk` (0-based)
 *   noscale=1     : do not use the scaling reduction on the first W column
 *   boxdepth      : only test for a box from this depth on (default 0 = test at every node)
 * Output: FOUND lines (at most PRINTLIM) and a final line "DONE ... found=N"; found=0 means no blocking
 * family exists (for this p; the choice of Z is arbitrary, any 3 distinct columns may be used).
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

static int p, FULL;
static int Z[3], W[16], nW;
static int ncls, cls[64][3];        /* class reps {0,a,b} */
static int c0list[64], nc0;
static int coord[16][3];             /* coords of v_w in basis v_z */
static long long nodes=0, boxchecks=0, found=0, leaves=0;
static int boxdepth=0;
static int assign[16];
#ifndef PRINTLIM
#define PRINTLIM 20
#endif

static int md(long long a){ a%=p; if(a<0)a+=p; return (int)a; }
static int inv(int a){ for(int b=1;b<p;b++) if(md((long long)a*b)==1) return b; return -1; }
static inline uint16_t rot(uint16_t m,int s){ if(!s) return m; return (uint16_t)(((m<<s)|(m>>(p-s)))&FULL); }

/* S[x*p+y] bitmask over z */
static void translate_or(const uint16_t *S, uint16_t *out, int tx,int ty,int tz){
  for(int x=0;x<p;x++){ int nx=(x+tx)%p;
    for(int y=0;y<p;y++){ int ny=(y+ty)%p; out[nx*p+ny] |= rot(S[x*p+y],tz);} }
}

/* does complement of S contain a combinatorial 3x3x3 box? */
static int has_box(const uint16_t *S){
  boxchecks++;
  uint16_t U[13*13]; int cnt[13];
  for(int x=0;x<p;x++){ cnt[x]=0; for(int y=0;y<p;y++){ U[x*p+y]=(uint16_t)(~S[x*p+y])&FULL; cnt[x]+=__builtin_popcount(U[x*p+y]); } }
  int xs[13], nx=0; for(int x=0;x<p;x++) if(cnt[x]>=9) xs[nx++]=x;
  if(nx<3) return 0;
  for(int a=0;a<nx;a++) for(int b=a+1;b<nx;b++){
    uint16_t P[13]; int good=0;
    for(int y=0;y<p;y++){ P[y]=U[xs[a]*p+y]&U[xs[b]*p+y]; if(__builtin_popcount(P[y])>=3) good++; }
    if(good<3) continue;
    for(int c=b+1;c<nx;c++){
      uint16_t R[13]; int ys[13], ny=0;
      for(int y=0;y<p;y++){ R[y]=P[y]&U[xs[c]*p+y]; if(__builtin_popcount(R[y])>=3) ys[ny++]=y; }
      if(ny<3) continue;
      for(int i=0;i<ny;i++) for(int j=i+1;j<ny;j++){ uint16_t q=R[ys[i]]&R[ys[j]]; if(__builtin_popcount(q)<3) continue;
        for(int k=j+1;k<ny;k++) if(__builtin_popcount(q&R[ys[k]])>=3) return 1; }
    }
  }
  return 0;
}

static void dfs(int depth, const uint16_t *S){
  nodes++;
  if(depth>=boxdepth || depth==nW){ if(!has_box(S)) return; }
  if(depth==nW){ leaves++; found++;
    if(found<=PRINTLIM){ printf("FOUND blocking W-assignment:"); for(int i=0;i<nW;i++) printf(" w%d:{0,%d,%d}",W[i],cls[assign[i]][1],cls[assign[i]][2]); printf("\n"); }
    return; }
  int w=depth; uint16_t N[13*13];
  for(int c=0;c<ncls;c++){
    assign[w]=c;
    memcpy(N,S,sizeof(uint16_t)*p*p);
    for(int e=1;e<=2;e++){ int a=cls[c][e];
      translate_or(S,N,md((long long)a*coord[w][0]),md((long long)a*coord[w][1]),md((long long)a*coord[w][2])); }
    dfs(depth+1,N);
  }
}

int main(int argc,char**argv){
  if(argc<5){fprintf(stderr,"usage\n");return 1;}
  p=atoi(argv[1]); FULL=(1<<p)-1; Z[0]=atoi(argv[2]);Z[1]=atoi(argv[3]);Z[2]=atoi(argv[4]);
  int chunk=0,nch=1,noscale=0; if(argc>=7){chunk=atoi(argv[5]);nch=atoi(argv[6]);} if(argc>=8) noscale=atoi(argv[7]);
  boxdepth = (argc>=9)? atoi(argv[8]) : 0;
  nW=0; for(int i=0;i<p;i++) if(i!=Z[0]&&i!=Z[1]&&i!=Z[2]) W[nW++]=i;
  /* classes: 0-containing 3-sets mod translation; rep = first {0,a,b} seen */
  static int seen[13][13]; memset(seen,0,sizeof seen); ncls=0;
  for(int a=1;a<p;a++) for(int b=a+1;b<p;b++){ if(seen[a][b]) continue;
    cls[ncls][0]=0;cls[ncls][1]=a;cls[ncls][2]=b; ncls++;
    int el[3]={0,a,b};
    for(int t=0;t<3;t++){ int x[3]; for(int j=0;j<3;j++) x[j]=md(el[j]-el[t]);
      int u=-1,v=-1; for(int j=0;j<3;j++) if(x[j]){ if(u<0)u=x[j]; else v=x[j]; }
      if(u>v){int tt=u;u=v;v=tt;} seen[u][v]=1; } }
  /* class id lookup */
  int clsid[13][13]; for(int a=0;a<p;a++)for(int b=0;b<p;b++)clsid[a][b]=-1;
  for(int c=0;c<ncls;c++){ int el[3]={0,cls[c][1],cls[c][2]};
    for(int t=0;t<3;t++){ int x[3]; for(int j=0;j<3;j++) x[j]=md(el[j]-el[t]);
      int u=-1,v=-1; for(int j=0;j<3;j++) if(x[j]){ if(u<0)u=x[j]; else v=x[j]; }
      if(u>v){int tt=u;u=v;v=tt;} clsid[u][v]=c; } }
  /* scaling orbits */
  int orb[64]; for(int c=0;c<ncls;c++) orb[c]=-1; nc0=0;
  for(int c=0;c<ncls;c++){ if(orb[c]>=0) continue; c0list[nc0]=c;
    for(int l=1;l<p;l++){ int a=md((long long)l*cls[c][1]), b=md((long long)l*cls[c][2]); int u=a<b?a:b, v=a<b?b:a; orb[clsid[u][v]]=nc0; }
    nc0++; }
  if(noscale){ nc0=ncls; for(int c=0;c<ncls;c++) c0list[c]=c; }
  /* coordinates: solve sum_j alpha_j (1,z_j,z_j^2) = (1,w,w^2) via Lagrange, then verify */
  for(int i=0;i<nW;i++){ int w=W[i];
    for(int j=0;j<3;j++){ long long num=1,den=1; for(int l=0;l<3;l++) if(l!=j){ num=num*md(w-Z[l])%p; den=den*md(Z[j]-Z[l])%p; }
      coord[i][j]=md(num*inv((int)den)); }
    for(int e=0;e<3;e++){ long long s=0; for(int j=0;j<3;j++){ long long pw=1; for(int r=0;r<e;r++) pw=pw*Z[j]%p; s+=coord[i][j]*pw; }
      long long pw=1; for(int r=0;r<e;r++) pw=pw*w%p; if(md(s)!=md(pw)){fprintf(stderr,"coord error\n");return 2;} } }
  printf("p=%d Z={%d,%d,%d} W=",p,Z[0],Z[1],Z[2]); for(int i=0;i<nW;i++) printf("%d ",W[i]);
  printf(" classes=%d first-column reps=%d (noscale=%d) chunk %d/%d boxdepth=%d\n",ncls,nc0,noscale,chunk,nch,boxdepth); fflush(stdout);
  /* first column W[0] restricted to c0list; chunk over (c0, class of W[1]) */
  uint16_t S0[13*13]; memset(S0,0,sizeof S0); S0[0]=1;
  long long job=0;
  for(int ci=0;ci<nc0;ci++){ int c=c0list[ci]; assign[0]=c;
    uint16_t S1[13*13]; memcpy(S1,S0,sizeof S0);
    for(int e=1;e<=2;e++){ int a=cls[c][e]; translate_or(S0,S1,md((long long)a*coord[0][0]),md((long long)a*coord[0][1]),md((long long)a*coord[0][2])); }
    for(int c1=0;c1<ncls;c1++){ if((job++)%nch!=chunk) continue; assign[1]=c1;
      uint16_t S2[13*13]; memcpy(S2,S1,sizeof S1);
      for(int e=1;e<=2;e++){ int a=cls[c1][e]; translate_or(S1,S2,md((long long)a*coord[1][0]),md((long long)a*coord[1][1]),md((long long)a*coord[1][2])); }
      dfs(2,S2);
    } }
  printf("DONE p=%d chunk %d/%d nodes=%lld boxchecks=%lld found=%lld\n",p,chunk,nch,nodes,boxchecks,found);
  return 0;
}
