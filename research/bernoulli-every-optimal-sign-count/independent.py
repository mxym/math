from math import gcd
import sys

def require(ok):
    if not ok:
        raise ValueError("nonintegral, normalization, or modal mismatch")

def calc(n,T):
    s=2*n*T
    r=n*T-n+1
    d=gcd(r,s)
    s//=d
    r//=d
    q=s-r
    uv=r*q
    sx=r*r+q*q
    rp=[r**i for i in range(n+1)]
    qp=[q**i for i in range(n+1)]
    best=-1
    hits=[]
    for l in range((n+1)//2,n+1):
        c=l*r*r+(n-l)*q*q
        a,b=0,qp[l]*rp[n-l]
        pool=0
        for j in range(n+1):
            if b==best:
                hits.append((2*l-n,j-(n-l)))
            if b>best:
                best=b
                hits=[(2*l-n,j-(n-l))]
            pool+=b
            if j==n:break
            quot,rem=divmod((c-sx*j)*b+uv*(n-j+1)*a,uv*(j+1))
            require(rem==0 and quot>0)
            a,b=b,quot
        require(pool==s**n)
    require(hits==[(T,(T-1)//2)])
stop=int(sys.argv[1]) if len(sys.argv)>1 else 149
num=0
for n in range(3,stop+1,2):
    for T in range(3,n+1,2):
        calc(n,T)
        num+=1
print("PASS independent differential-coefficient recurrence:",num,"exact bias/imbalance pairs through odd n =",stop)
