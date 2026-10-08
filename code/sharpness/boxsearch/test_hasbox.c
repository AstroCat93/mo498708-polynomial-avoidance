/* test_hasbox.c -- validates has_box() of boxsearch.c against a brute-force search over all pairs of
 * 3-sets (A,B) on random, realistic-sumset and planted-box inputs.  Written by the same independent
 * verifier as boxsearch.c.  usage: test_hasbox p ntests   (compile in this directory: it #includes boxsearch.c)
 */
#define main bs_main
#include "boxsearch.c"
#undef main
/* brute force: exists 3-sets A,B,C with A x B x C inside complement of S */
static int brute_box(const uint16_t *S){
  int sets[400],ns=0; for(int m=0;m<(1<<p);m++) if(__builtin_popcount(m)==3) sets[ns++]=m;
  for(int a=0;a<ns;a++) for(int b=0;b<ns;b++){
    /* zmask = intersection over x in A, y in B of complement rows */
    uint16_t zm=FULL;
    for(int x=0;x<p;x++) if(sets[a]>>x&1) for(int y=0;y<p;y++) if(sets[b]>>y&1) zm&=(uint16_t)(~S[x*p+y])&FULL;
    if(__builtin_popcount(zm)>=3) return 1; }
  return 0;
}
static unsigned long long rs=88172645463325252ULL; static unsigned rnd(){ rs^=rs<<13; rs^=rs>>7; rs^=rs<<17; return (unsigned)(rs>>11); }
int main(int argc,char**argv){
  p=atoi(argv[1]); FULL=(1<<p)-1; int ntest=atoi(argv[2]);
  int agree=0,dis=0,pos=0;
  for(int t=0;t<ntest;t++){
    uint16_t S[13*13]; memset(S,0,sizeof S); int mode=t%3;
    if(mode==0){ /* realistic: sumset of k random columns with random direction vectors */
      S[0]=1; int k=3+rnd()%5;
      for(int j=0;j<k;j++){ int v[3]={rnd()%p,rnd()%p,rnd()%p}; int a=1+rnd()%(p-1), b; do b=1+rnd()%(p-1); while(b==a);
        uint16_t N[13*13]; memcpy(N,S,sizeof N);
        translate_or(S,N,a*v[0]%p,a*v[1]%p,a*v[2]%p); translate_or(S,N,b*v[0]%p,b*v[1]%p,b*v[2]%p); memcpy(S,N,sizeof N);} }
    else { int dens=50+rnd()%50; for(int i=0;i<p*p;i++) for(int z=0;z<p;z++) if((int)(rnd()%100)<dens) S[i]|=1<<z;
      if(mode==2){ /* plant a box (clear it) sometimes */ int A=0,B=0,C=0; while(__builtin_popcount(A)<3)A|=1<<(rnd()%p); while(__builtin_popcount(B)<3)B|=1<<(rnd()%p); while(__builtin_popcount(C)<3)C|=1<<(rnd()%p);
        for(int x=0;x<p;x++) if(A>>x&1) for(int y=0;y<p;y++) if(B>>y&1) S[x*p+y]&=~C; } }
    int h=has_box(S), b=brute_box(S); if(h==b) agree++; else dis++; pos+=b; }
  printf("p=%d tests=%d agree=%d disagree=%d brute-positive=%d\n",p,ntest,agree,dis,pos);
}
