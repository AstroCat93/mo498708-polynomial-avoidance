# Verify poster's constructions for d = p-2 and d = p-1 via the moment (dual) DP:
# blocking  <=>  no y in prod C_i (C_i = complement of A_i) with sum_i y_i i^j = 0 for j < k = p-d.
def blocking_dual(p,d,A):
    k=p-d
    C=[[c for c in range(p) if c not in A[i]] for i in range(p)]
    reach={tuple([0]*k)}
    for i in range(p):
        v=[1 if j==0 else pow(i,j,p) for j in range(k)]
        reach={tuple((s[j]+c*v[j])%p for j in range(k)) for s in reach for c in C[i]}
    return tuple([0]*k) not in reach
for p in [5,7,11,13,17,19,23]:
    g=[pow(i,p-2,p) for i in range(p)]      # g(x)=x^{p-2} has degree p-2 (the poster's d=p-2 construction)
    Apm2=[[a for a in range(p) if a not in (g[i],(g[i]+1)%p)] for i in range(p)]
    b=[0]*p; b[0]=1
    Apm1=[[a for a in range(p) if a!=b[i]] for i in range(p)]
    print(p,'d=p-2:',blocking_dual(p,p-2,Apm2),' d=p-1:',blocking_dual(p,p-1,Apm1))
