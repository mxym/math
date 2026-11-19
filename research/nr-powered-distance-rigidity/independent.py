#!/usr/bin/env python3
"""Independent exhaustive certificate. Angle used here is z=sin²(phi/2)."""
from math import comb, factorial
def require(ok,msg):
    if not ok: raise ArithmeticError(msg)
def conv(A,B):
    return [sum(A[h]*B[i-h] for h in range(max(0,i-len(B)+1),min(len(A)-1,i)+1)) for i in range(len(A)+len(B)-1)]
def divide(A,B):
    # Descending exact long division.
    R=A[:]; Q=[0]*(len(A)-len(B)+1)
    for j in reversed(range(len(Q))):
        q,r=divmod(R[len(B)-1+j],B[-1]);require(r==0,'inexact quotient')
        for i,b in enumerate(B): R[i+j]-=q*b
        Q[j]=q
    require(not any(R),'nonzero remainder')
    return Q
def positive_control(c,maxdepth=14):
    if min(c)>0:return 0,1
    require(maxdepth>0 and c[0]>0 and c[-1]>0,'uncertified interval')
    K=len(c)-1;left=[];right=[]
    for i in range(K+1):
        # c entries at stage i = 2**i times true De Casteljau row.
        left.append(c[0]<<(K-i));right.append(c[-1]<<(K-i))
        c=[p+q for p,q in zip(c,c[1:])]
    a,u=positive_control(left,maxdepth-1);b,v=positive_control(right[::-1],maxdepth-1)
    return 1+max(a,b),u+v
def run(n):
    k=n-1
    L=(2 if k<=12 else 3 if k<=15 else 8 if k==16 else 14)*k
    ds=[[comb(k,l+m)*comb(k,l) for l in range(k-m+1)] for m in range(n)]
    D=[1]
    for p in ds[1:]:D=conv(D,p)
    Q=[divide(D,p) for p in ds[1:]]; E=len(D)
    require(E==1+k*(k-1)//2,'scale degree')
    # Compile coefficients from each monomial t^h BEFORE homogeneous t-transform.
    # Transform coefficient by repeated sums of t^d, not a hockey-stick formula.
    W=[[0]*L for h in range(2*k+2)]
    for b in range(L):
      w=0
      for h in reversed(range(L)):
        w+=comb(L-1-h,b-h) if b>=h else 0
        if h<len(W):W[h][b]=w
    # Re(exp(i*m*phi)) under z=sin(phi/2)^2, with degree elevated to k:
    # cos(m*phi)=sum_a (-1)^a C(2m,2a) z^a(1-z)^(m-a).
    # Multiply by (z+(1-z))^(k-m) to degree k; divide C(k,i) to obtain
    # Bernstein control values, all scaled simultaneously by k! to be integers.
    ang=[]
    for m in range(n):
      ap=conv([(-1)**a*comb(2*m,2*a) for a in range(m+1)],[comb(k-m,a) for a in range(k-m+1)])
      ang.append([v*factorial(i)*factorial(k-i) for i,v in enumerate(ap)])
    maxdep=leaves=count=0
    for b in range(L):
      # Compute s-polynomial by direct convolution, independently per harmonic.
      freq=[[n*c*W[0][b] for c in D]]
      for m in range(1,n):
        G=[v*W[m+2*l][b] for l,v in enumerate(ds[m])]
        freq.append([2*(n-m)*v for v in conv(G,Q[m-1])])
      for e in range(E):
        c=[sum(freq[m][e]*ang[m][i] for m in range(n)) for i in range(n)]
        dep,ls=positive_control(c)
        maxdep=max(maxdep,dep);leaves+=ls;count+=1
    print(f'PASS N={n:2} polynomials={count:5} certified_intervals={leaves:6} max_depth={maxdep}',flush=True)
    return count,leaves
if __name__=='__main__':
 A=[run(n) for n in range(2,19)]
 require(sum(q[0] for q in A)==65399,'missing cases')
 print(f'PASS {sum(q[0] for q in A)} entire polynomials on the closed angular interval; {sum(q[1] for q in A)} positive-control subintervals.')
