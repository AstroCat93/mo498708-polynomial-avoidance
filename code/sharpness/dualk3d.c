/* dualk3d: exhaustive search for blocking families with d = p-3 (complements C_i, |C_i| = 3).
   Identical to dualk3c except that it also uses the domain-scaling symmetry described below.
   Blocking <=> no y in prod_i C_i with sum_i y_i v_i = 0, v_i = (1,i,i^2) (0^0 = 1)
            <=> no f in F_p[x], deg f <= p-4, with f(i) in C_i for all i.
   Reformulation: solution.md, Lemma 3.1.  Normalisation N2 (WLOG; proof: solution.md, Lemma 3.4):
     t = minimal AGL(1,p)-type among the C_i; column 0 has type t and C_0 = R_t (lex-min representative);
     all columns have type >= t;  0 in C_w for every w in W = F_p \ Z (Z = 3 chosen nonzero columns, argv);
     for w in W\{0}: C_w is the lex-min among its translates containing 0.
   Symmetry (last part of Lemma 3.4): if alpha*Z = Z for some alpha in F_p^*, the map C_i -> C_{alpha*i}
     preserves the normal form and permutes the Z-columns, so only the lexicographically least box in
     each orbit is searched; the others are counted as skipped_by_symmetry.
     (For p = 13, Z = {1,3,9} is preserved by alpha = 3 and alpha = 9.)
   Search: for every box (C_z)_{z in Z} (type >= t), DFS over W\{0}, keeping S = sum_{assigned w} C_w v_w,
   which must avoid F = -sum_z C_z v_z (27 points).  Since 0 in C_w, S only grows => prune immediately.
   Usage: dualk3d p t z1 z2 z3 boxStart boxStep [list] */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#define MAXP 23
#define MAXN (MAXP*MAXP*MAXP)
#define NWORD ((MAXN+63)/64)
static int p,N;
static int typ3[MAXP][MAXP][MAXP];
static int rep[64][3], ntypes;
static int vv[MAXP][3];
static int *addtab[MAXP][MAXP]; /* addtab[i][u][s] = s + u v_i */
static int Wc[MAXP], nW;      /* Wc[0]=0 */
static int pairs[MAXP*MAXP][2], npairs;
static int Fpts[27];
static int Fsh[MAXP][MAXP][27]; /* Fsh[j][u][q] = Fpts[q] - u v_{Wc[j]} */
typedef struct { uint64_t w[NWORD]; } bs;
static int NW64;
static inline int getb(const bs*x,int i){ return (x->w[i>>6]>>(i&63))&1; }
static inline void setb(bs*x,int i){ x->w[i>>6]|=1ULL<<(i&63); }
static long long nodes; static int assignU[MAXP][2];
static inline int allowed(const bs*S,int j,int u){ const int*f=Fsh[j][u]; for(int q=0;q<27;q++) if(getb(S,f[q])) return 0; return 1; }
static void shift_or(bs*dst,const bs*src,int i,int u){ const int*t=addtab[i][u];
  for(int k=0;k<NW64;k++){ uint64_t w=src->w[k]; while(w){ int b=__builtin_ctzll(w); w&=w-1; setb(dst,t[k*64+b]); } } }
static int dfs(const bs*S,unsigned done){
  nodes++;
  int best=-1,bestc=1<<30; unsigned char al[MAXP][MAXP]; 
  for(int j=1;j<nW;j++){ if(done>>j&1) continue;
    for(int u=1;u<p;u++) al[j][u]=allowed(S,j,u);
    int c=0; for(int q=0;q<npairs;q++) if(al[j][pairs[q][0]]&&al[j][pairs[q][1]]) c++;
    if(!c) return 0; if(c<bestc){bestc=c;best=j;} }
  if(best<0) return 1;
  int i=Wc[best];
  for(int q=0;q<npairs;q++){ int u=pairs[q][0],u2=pairs[q][1]; if(!(al[best][u]&&al[best][u2])) continue;
    bs S2=*S; shift_or(&S2,S,i,u); shift_or(&S2,S,i,u2); assignU[best][0]=u; assignU[best][1]=u2;
    if(dfs(&S2,done|(1u<<best))) return 1; }
  return 0; }
static void sort3(int*x){ for(int i=0;i<3;i++)for(int j=i+1;j<3;j++) if(x[j]<x[i]){int t=x[i];x[i]=x[j];x[j]=t;} }
int main(int argc,char**argv){
  p=atoi(argv[1]); int t=atoi(argv[2]); int Z[3]={atoi(argv[3]),atoi(argv[4]),atoi(argv[5])};
  long long bstart=atoll(argv[6]),bstep=atoll(argv[7]); int listmode=argc>8;
  N=p*p*p; NW64=(N+63)/64;
  /* types */
  static int keys[4096]; int nk=0;
  for(int a=0;a<p;a++)for(int b=a+1;b<p;b++)for(int c=b+1;c<p;c++){
    int best=1<<30;
    for(int m=1;m<p;m++)for(int s=0;s<p;s++){ int x[3]={(m*a+s)%p,(m*b+s)%p,(m*c+s)%p}; sort3(x); int key=(x[0]*p+x[1])*p+x[2]; if(key<best) best=key; }
    int id=-1; for(int q=0;q<nk;q++) if(keys[q]==best) id=q; if(id<0){id=nk;keys[nk++]=best;}
    typ3[a][b][c]=best; }
  /* rank keys */
  for(int q=0;q<nk;q++)for(int r=q+1;r<nk;r++) if(keys[r]<keys[q]){int tt=keys[q];keys[q]=keys[r];keys[r]=tt;}
  ntypes=nk;
  for(int a=0;a<p;a++)for(int b=a+1;b<p;b++)for(int c=b+1;c<p;c++){ int k=typ3[a][b][c]; for(int q=0;q<nk;q++) if(keys[q]==k) typ3[a][b][c]=q; }
  for(int q=0;q<nk;q++){ rep[q][0]=keys[q]/(p*p); rep[q][1]=(keys[q]/p)%p; rep[q][2]=keys[q]%p; }
  for(int i=0;i<p;i++){ vv[i][0]=1; vv[i][1]=i; vv[i][2]=(i*i)%p; }
  for(int i=0;i<p;i++)for(int u=0;u<p;u++){ addtab[i][u]=malloc(sizeof(int)*N);
    for(int s=0;s<N;s++){ int a=s%p,b=(s/p)%p,c=s/(p*p); a=(a+u*vv[i][0])%p; b=(b+u*vv[i][1])%p; c=(c+u*vv[i][2])%p; addtab[i][u][s]=a+p*b+p*p*c; } }
  /* W columns */
  nW=0; Wc[nW++]=0; for(int i=1;i<p;i++) if(i!=Z[0]&&i!=Z[1]&&i!=Z[2]) Wc[nW++]=i;
  if(nW!=p-3||Z[0]==0||Z[1]==0||Z[2]==0){ fprintf(stderr,"bad Z\n"); return 1; }
  /* canonical W sets {0,u,u2} with type>=t */
  npairs=0;
  for(int u=1;u<p;u++)for(int u2=u+1;u2<p;u2++){ if(typ3[0][u][u2]<t) continue;
    int S1[3]={(p-u)%p,0,(u2-u)%p}, S2[3]={(p-u2)%p,(u-u2+p)%p,0}; sort3(S1); sort3(S2);
    int key=u*p+u2, k1=S1[1]*p+S1[2], k2=S2[1]*p+S2[2];
    if(k1<key||k2<key) continue; pairs[npairs][0]=u; pairs[npairs][1]=u2; npairs++; }
  static int trip[4096][3]; int nt=0;
  for(int a=0;a<p;a++)for(int b=a+1;b<p;b++)for(int c=b+1;c<p;c++) if(typ3[a][b][c]>=t){trip[nt][0]=a;trip[nt][1]=b;trip[nt][2]=c;nt++;}
  long long nbox=(long long)nt*nt*nt;
  fprintf(stderr,"p=%d types=%d t=%d R_t={%d,%d,%d} Z={%d,%d,%d} Wpairs=%d triples=%d boxes=%lld\n",p,ntypes,t,rep[t][0],rep[t][1],rep[t][2],Z[0],Z[1],Z[2],npairs,nt,nbox);
  /* domain-scaling symmetry: alpha with alpha*Z = Z permutes the box columns; keep only lex-min boxes */
  int nal=0, perm[MAXP][3];
  for(int al=2;al<p;al++){ int img[3]; for(int q=0;q<3;q++) img[q]=(al*Z[q])%p;
    int ok=1, pm[3]; for(int q=0;q<3;q++){ pm[q]=-1; for(int r=0;r<3;r++) if(img[q]==Z[r]) pm[q]=r; if(pm[q]<0) ok=0; }
    /* new box: C'_{Z[q]} = C_{al*Z[q]} = C_{Z[pm[q]]} */
    if(ok){ for(int q=0;q<3;q++) perm[nal][q]=pm[q]; nal++; } }
  fprintf(stderr,"scaling symmetries preserving Z: %d\n",nal);
  long long checked=0,tot=0,skipped=0; int found=0;
  for(long long bi=bstart;bi<nbox;bi+=bstep){
    long long ix[3]={bi/((long long)nt*nt),(bi/nt)%nt,bi%nt};
    { int skip=0; for(int s=0;s<nal;s++){ long long jx[3]; for(int q=0;q<3;q++) jx[q]=ix[perm[s][q]];
        long long bj=(jx[0]*nt+jx[1])*nt+jx[2]; if(bj<bi){skip=1;break;} }
      if(skip){ skipped++; if(listmode) printf("BOX %lld S\n",bi); continue; } }
    int *A=trip[ix[0]],*B=trip[ix[1]],*C=trip[ix[2]];
    int q=0; for(int x=0;x<3;x++)for(int y=0;y<3;y++)for(int z=0;z<3;z++){
      int s=addtab[Z[0]][A[x]][0]; s=addtab[Z[1]][B[y]][s]; s=addtab[Z[2]][C[z]][s];
      int a=s%p,b=(s/p)%p,c=s/(p*p); Fpts[q++]=((p-a)%p)+p*((p-b)%p)+p*p*((p-c)%p); }
    for(int j=0;j<nW;j++) for(int u=0;u<p;u++) for(int q2=0;q2<27;q2++) Fsh[j][u][q2]=addtab[Wc[j]][(p-u)%p][Fpts[q2]];
    bs S; memset(&S,0,sizeof S); int ok=1;
    for(int x=0;x<3;x++){ int s=addtab[0][rep[t][x]][0]; for(int q2=0;q2<27;q2++) if(Fpts[q2]==s) ok=0; setb(&S,s); }
    checked++;
    int res=0; nodes=0;
    if(ok) res=dfs(&S,1u);
    tot+=nodes;
    if(listmode) printf("BOX %lld %d\n",bi,res);
    if(res){ found++; printf("FOUND p=%d C_0={%d,%d,%d}",p,rep[t][0],rep[t][1],rep[t][2]);
      for(int j=1;j<nW;j++) printf(" C_%d={0,%d,%d}",Wc[j],assignU[j][0],assignU[j][1]);
      printf(" C_%d={%d,%d,%d} C_%d={%d,%d,%d} C_%d={%d,%d,%d}\n",Z[0],A[0],A[1],A[2],Z[1],B[0],B[1],B[2],Z[2],C[0],C[1],C[2]); fflush(stdout);
      if(!listmode && found>=5) break; }
  }
  printf("DONE p=%d t=%d Z={%d,%d,%d} start=%lld step=%lld boxes_checked=%lld skipped_by_symmetry=%lld nodes=%lld found=%d\n",p,t,Z[0],Z[1],Z[2],bstart,bstep,checked,skipped,tot,found);
  return 0; }
