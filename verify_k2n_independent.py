from math import comb, cos, pi
from itertools import pairwise
def choose(n,i): return comb(n,i) if 0<=i<=n else 0
def transformed(N):
    q=1<<N
    a=[q*choose(N-1,i)+((q//2)-(1<<(N-i)))*choose(N-1,i-1) for i in range(N+1)]
    padded=[0]+a+[0]
    return [x*x-padded[i]*padded[i+2] for i,x in enumerate(a)]
def sign_at(b,k,q):
    if k==0:return b[0]
    if k==q:return (-1)**(len(b)-1)*b[-1]
    # Direct homogeneous sum, iterating monomials in increasing power of -k.
    a=-k; c=q-k; d=len(b)-1
    v=c**d
    out=0
    for coefficient in b:
        out+=coefficient*v
        v=v//c*a
    return out
def guide(m):
    # Jacobi matrix determinant recurrence, monic, at cosine grid points.
    beta=[(j*(j+4))/((2*j+3)*(2*j+5)) for j in range(1,m)]
    def f(t):
        x=cos(t); p,q=1.0,x
        for y in beta:
            p,q=q,x*q-y*p
        return q
    grid=12*m+31
    hint=[]
    a=0.; fa=f(a)
    for k in range(1,grid+1):
        b=k*pi/grid; fb=f(b)
        if fa==0.0:
            hint.append(a)
        elif fa*fb<0.0:
            lo,hi=a,b; flo=fa
            for _ in range(25):
                mid=lo+(hi-lo)/2; fm=f(mid)
                if fm==0.0:lo=hi=mid;break
                if flo*fm<0:hi=mid
                else:lo=mid;flo=fm
            hint.append((lo+hi)/2)
        a=b;fa=fb
    assert len(hint)==m,(m,len(hint))
    return hint
def low(N,b):
    q=4096
    want=-1;k=1;got=[0]
    while len(got)<N and k<q:
        if want*sign_at(b,k,q)>0:
            got.append(k);want=-want
        k+=1
    return got+[q],q
c=0
for N in range(2,200):
    b=transformed(N)
    assert b[0]>0 and b[-1]>0
    if N<=6:
        ks,q=low(N,b)
    else:
        q=2**27
        ks=[0,*[round(q*(1-cos(t))/2) for t in guide(N-1)],q]
    assert len(ks)==N+1 and all(a<b for a,b in pairwise(ks)),(N,ks)
    for i,k in enumerate(ks):
        assert (-1)**i*sign_at(b,k,q)>0,(N,i,k)
    c+=len(ks)
    if N%25==0:print('Independent finite check through',N,flush=True)
assert c==20097
print('PASS independent finite range,',c,'integer sign verifications')
