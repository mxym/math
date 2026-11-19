from math import comb
from functools import cache
# No input files, no network, no external dependencies.
# N=2,...,18 inclusive; no assert statements or floating arithmetic.
# Lines beginning PASS are printed after all tests for that order succeed.
def mul(a,b):
 c=[0]*(len(a)+len(b)-1)
 for i,v in enumerate(a):
  for j,w in enumerate(b): c[i+j]+=v*w
 return c
def d_all(k,m):return [comb(k,l)*comb(k,l+m) for l in range(k-m+1)]
def prod(fs):
 out=[1]
 for f in fs:out=mul(out,f)
 return out
@cache
def cheb(m):
 if m<=1:return [1] if m==0 else [0,1]
 a=[0]+[2*i for i in cheb(m-1)]
 for j,v in enumerate(cheb(m-2)):a[j]-=v
 return a
def bernprep(a,b,k):
 # x=a+(b-a)z. Return unnormalized homogeneous coefficient in x=(a+bu)/(1+u)
 return [[sum(comb(m,h)*a**(m-h)*b**h*comb(k-m,j-h) for h in range(max(0,j-(k-m)),min(j,m)+1)) for m in range(k+1)] for j in range(k+1)]
def rec(v,depth=0):
 if min(v)>0:return depth
 if v[0]<=0 or v[-1]<=0:return -1
 if depth==15:return -1
 k=len(v)-1
 # v are unnormalized homogeneous coefficients. Subdivide via left angle=(a+(a+b)/2 u)/(1+u). 
 # polynomial C(1+u/2,u/2) times 2^k; reverse coefficients to mirror the other half.
 left=[2**(k-j)*sum(v[i]*comb(k-i,j-i) for i in range(j+1)) for j in range(k+1)]
 right=list(reversed([2**(k-j)*sum(v[k-i]*comb(k-i,j-i) for i in range(j+1)) for j in range(k+1)]))
 l=rec(left,depth+1)
 if l<0:return -1
 r=rec(right,depth+1)
 return -1 if r<0 else max(l,r)
def process(n):
 k=n-1;T=k*(2 if n<=13 else 3 if n<=16 else 8 if n==17 else 14)
 ds=[d_all(k,m) for m in range(1,n)];Den=prod(ds);dsout=[prod(ds[:m-1]+ds[m:]) for m in range(1,n)]
 # t=u/(1+u), deg T-1. (1+u)^(T-1) sum_{d=j}^{T-1} (u/(1+u))^d has coeff C(T-j,b-j).
 # hockey stick sum over d from j to b of C(T-1-d,b-d)=C(T-j,b-j)
 tr=bernprep(-1,1,k)
 ChebB=[[sum(a[i]*p for i,p in enumerate(cheb(m))) for a in tr] for m in range(k+1)]
 maxdepth=0;cnt=0
 for b in range(T):
  for e,D in enumerate(Den):
   coeff=[n*D*comb(T,b)]
   for m in range(1,n):
    coef=0
    for l,c in enumerate(ds[m-1]):
     j=m+2*l
     if j>b or not 0<=e-l<len(dsout[m-1]):continue
     coef+=c*dsout[m-1][e-l]*comb(T-j,b-j)
    coeff.append(2*(n-m)*coef)
   V=[sum(c*ChebB[m][i] for m,c in enumerate(coeff)) for i in range(k+1)]
   depth=rec(V)
   if depth<0:raise ValueError(f'Uncertified: N={n}, b={b}, e={e}')
   cnt+=1;maxdepth=max(maxdepth,depth)
 if cnt!=T*(1+k*(k-1)//2):raise ValueError('Unexpected certificate size')
 print(f'PASS N={n} L={T} coefficient-polynomials={cnt} maxdepth={maxdepth}',flush=True)
 return cnt
if __name__=='__main__':
 count=sum(process(n) for n in range(2,19))
 print('PASS complete distinct (N,b,e) triples:', count)
