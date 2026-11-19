"""Exact integer mirror masses and prefixes. This verifies finitely many examples."""
from math import comb
def require(expr): 
    if not expr: raise ArithmeticError("integer check failed")
cases=terms=0
for n in range(2,131):
 for m in range(1,n//2+1):
    u=n-m
    B=[comb(n,j)*m**j*u**(n-j) for j in range(n+1)]
    require(sum(B)==n**n)
    D=[(B[m-j] if j<=m else 0)-B[m+j] for j in range(1,u+1)]
    A=[sum(D[i:]) for i in range(u)]
    require(A[:m]==[sum(B[:m-i+1])-sum(B[m+i:]) for i in range(1,m+1)])
    require(sum(A)==0 and min(A[0],0)==0)
    seen=False
    for ai in A[:m]:
        if ai<0: seen=True
        if seen: require(ai<=0)
    require(all(sum(A[:j])>=0 for j in range(1,m+1)))
    for j in range(m):
        require(B[m-j-1]*B[m+j]*m*m*(u*(u+1)-j*(j+1))==B[m+j+1]*B[m-j]*u*u*(m*(m+1)-j*(j+1)))
    cases+=1;terms+=m
print('PASS',cases,'binomial laws;',terms,'reflected ratio and prefix checks')
