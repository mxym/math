"""Exact polynomial recurrence proof audit for the new elementary rank determinant.

Checks Δ^r G_0(t)=(t-1)^r [u^(m-r)] Z_{n-2r}(u,t)
for all ranks up to 10 and several n, without any algebraic eigenvalue.
"""
from math import comb
from check_all_k_orbital_compression import plus,mul,power

def trace_list(n,m):
    Z=[{(0,0):2},{(0,0):1,(1,1):1}]
    A={(0,0):1,(1,1):1}
    D={(1,1):1,(1,0):-1}
    for L in range(2,n+1):
        Z.append(plus(mul(A,Z[-1],m),mul(D,Z[-2],m),-1))
    return Z

def from_u(P,r):
    return {i:v for (u,i),v in P.items() if u==r and v}

def poly_add(A,B,sgn=1):
    C=dict(A)
    for j,v in B.items():C[j]=C.get(j,0)+sgn*v
    return {j:v for j,v in C.items() if v}

def poly_mul(A,B):
    C={}
    for j,v in A.items():
        for k,w in B.items():C[j+k]=C.get(j+k,0)+v*w
    return {j:v for j,v in C.items() if v}

def poly_pow_minus_one(r):
    return {j:comb(r,j)*(-1)**(r-j) for j in range(r+1)}

def run(m,n):
    Z=trace_list(n,m)
    G=[]
    for j in range(m):
        L=n-j
        fixed=power({(0,0):1,(1,1):1},j,m)
        G.append(from_u(mul(fixed,Z[L],m),m))
    for r in range(m):
        diff={}
        for j in range(r+1):
            diff=poly_add(diff,G[j],(-1)**(r-j)*comb(r,j))
        rhs=poly_mul(poly_pow_minus_one(r),from_u(Z[n-2*r],m-r))
        assert diff==rhs,(m,n,r,diff,rhs)
        diag=sum(coef*comb(deg,r) for deg,coef in diff.items())
        # coefficient of (t-1)^r == derivative/r!
        assert diag==comb(n-2*r,m-r),(m,n,r,diag)
    return m
if __name__=='__main__':
    count=0
    for m in range(1,11):
        for n in (2*m,2*m+1,2*m+4):
            run(m,n);count+=1
    print('ELEMENTARY RECURRENCE FULL-RANK IDENTITY PASSED',count,'PARAMETER PAIRS')
