"""Exact small-column gap checks for the all-orders induction; no floating point."""
from functools import lru_cache
from math import comb
K0=128
C=16
@lru_cache(None)
def A(n,k):
    if k>n:return 0
    if k<4:return comb(n,k)
    l=n//2;h=n-l;a=k//2;b=k-a
    return A(l,k)+A(h,k)+A(l,a)*A(h,b)+(A(l,b)*A(h,a) if a!=b else 0)
def main():
    cnt=quant=mx=0
    for j in range(1,K0):
        A.cache_clear()
        for n in range(j+1,2*j*j):
            an,bn=A(n,j),A(n,j+1)
            if min(an,bn)<=0:raise ArithmeticError(("support",n,j))
            det=A(n-1,j)*bn-A(n-1,j+1)*an
            if det<0:raise ArithmeticError(("minor",n,j,det))
            cnt+=1
            if n>=2*j-1:
                if det*(C*n*j*j)<an*bn:
                    raise ArithmeticError(("quantitative",n,j,det,an,bn))
                quant+=1
            mx=max(mx,n)
    print(f"Exact base: {cnt} adjacent minors and {quant} quantitative gaps; largest n={mx}; k<128.")
    print("PASS (integer arithmetic).")
if __name__=="__main__":main()
