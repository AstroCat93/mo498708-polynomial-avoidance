/* brute7.c -- independent brute force at p=7 (d=4), written by the same verifier as boxsearch.c.
   For each W-assignment of lex-first class reps,
   decide by enumerating ALL Z-boxes (arbitrary 3-sets) and ALL polynomials of degree<=3
   whether some family with C_w=rep_w blocks (no f with f(i) in C_i for all i).
   usage: brute7 z1 z2 z3   -- compare TOTAL with `boxsearch 7 z1 z2 z3 0 1 1` (found=...) */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define P 7
int main(int argc,char**argv){
  int Z[3]={atoi(argv[1]),atoi(argv[2]),atoi(argv[3])}; int W[4],nW=0;
  for(int i=0;i<P;i++) if(i!=Z[0]&&i!=Z[1]&&i!=Z[2]) W[nW++]=i;
  /* classes: lex-first {0,a,b} */
  int reps[10][3],nr=0, seen[P][P]; memset(seen,0,sizeof seen);
  for(int a=1;a<P;a++)for(int b=a+1;b<P;b++){ if(seen[a][b])continue; reps[nr][0]=0;reps[nr][1]=a;reps[nr][2]=b;nr++;
    int e[3]={0,a,b}; for(int t=0;t<3;t++){int u=-1,v=-1; for(int j=0;j<3;j++){int x=((e[j]-e[t])%P+P)%P; if(x){if(u<0)u=x;else v=x;}} if(u>v){int q=u;u=v;v=q;} seen[u][v]=1;} }
  int sets[35],ns=0; for(int m=0;m<(1<<P);m++) if(__builtin_popcount(m)==3) sets[ns++]=m;
  static int val[2401][P]; int np=0;
  for(int c0=0;c0<P;c0++)for(int c1=0;c1<P;c1++)for(int c2=0;c2<P;c2++)for(int c3=0;c3<P;c3++){
    for(int i=0;i<P;i++) val[np][i]=(c0+c1*i+c2*i*i+c3*i*i*i)%P; np++; }
  int total=0;
  for(int A=0;A<nr*nr*nr*nr;A++){ int t=A, mask[P];
    for(int k=0;k<4;k++){ int r=t%nr; t/=nr; mask[W[k]]=(1<<reps[r][0])|(1<<reps[r][1])|(1<<reps[r][2]); }
    int blocking=0;
    for(int x=0;x<ns && !blocking;x++)for(int y=0;y<ns && !blocking;y++)for(int z=0;z<ns && !blocking;z++){
      mask[Z[0]]=sets[x];mask[Z[1]]=sets[y];mask[Z[2]]=sets[z];
      int av=0; for(int f=0;f<np;f++){ int ok=1; for(int i=0;i<P;i++) if(!((mask[i]>>val[f][i])&1)){ok=0;break;} if(ok){av=1;break;} }
      if(!av) blocking=1; }
    if(blocking){ total++; printf("FOUND blocking W-assignment:"); t=A; for(int k=0;k<4;k++){int r=t%nr;t/=nr; printf(" w%d:{0,%d,%d}",W[k],reps[r][1],reps[r][2]);} printf("\n"); }
  }
  printf("TOTAL blocking W-assignments %d of %d\n",total,nr*nr*nr*nr);
}
