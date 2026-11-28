
"""Exact scalar certificate for the large-minimum part of the 5x+1 theorem."""
from fractions import Fraction as F

M=21
X=1<<29
DEN=3*X
LMAX=F(M,DEN)
Q17=(138463487,59632978)
Q18=(241187130,103873643)
Q19=(1103212007,475127550)
Q20=(1344399137,579001193)
Q27=(19293579461887,8309292395561)
Q28=(53548351813079,23062019849360)

def log_interval(x,n=64):
    t=(x-1)/(x+1)
    p=t
    lower=F(0)
    for j in range(n):
        lower+=2*p/(2*j+1)
        p*=t*t
    return lower, lower+2*p/((2*n+1)*(1-t*t))

L2,U2=log_interval(F(2))
L54,U54=log_interval(F(5,4))
L5,U5=2*L2+L54,2*U2+U54

def gap(pair):
    p,k=pair
    assert p>=2*k>0
    return (p-2*k)*L2-k*U54,(p-2*k)*U2-k*L54

def bracket(up,down,cut,lower):
    p,k=up
    q,l=down
    assert p*l-q*k==1
    assert k+l>=cut
    assert gap(up)[0]>lower>0 and gap(down)[1]<0

def exp_lower(x):
    t=total=F(1)
    for j in range(1,25):
        t*=x/j; total+=t
    return total

def main():
    assert L2>F(69,100)
    assert F(2434,100)*U5<40
    rho=F(2321929,1000000)
    assert U5/L2<rho
    S=[F(0)]
    for j in range(M):
        S.append(1+rho*S[-1])
    SMAX=36444000
    assert S[M]<SMAX
    a=F(3,4)
    assert (rho-1)*a<F(1983,2000)
    assert (1-F(1983,2000))*L2/2>F(1,400)
    assert exp_lower(F(3))>20
    # For K>=3*10^13, K*ln(2)/S - 4 > 40*(ln(K)+2)^2.
    # It holds at the endpoint and the difference is increasing.
    start=3*10**13
    assert F(69,100)*start/SMAX-4>40*44**2
    assert F(69,100)/SMAX>F(80*44,start)
    bracket(Q27,Q28,start,F(28,10**16))
    # K>=2.1e9 implies lambda<28*e^-39<2.8e-15.
    k1=2100000000
    assert F(69,100)*k1/SMAX>39
    assert F(28,20**13)<F(28,10**16)
    up=tuple(u+2*v for u,v in zip(Q19,Q20))
    bracket(up,Q20,k1,F(110,10**11))
    # K>=1.3e9 implies lambda<28*e^-24<1.10e-9.
    k2=1300000000
    assert F(69,100)*k2/SMAX>24
    assert F(28,20**8)<F(110,10**11)

    p,k=Q17; q,l=Q18
    assert p*l-q*k==1
    alo,ahi=gap(Q17); blo,bhi=gap(Q18); b=-blo
    assert alo>0 and bhi<0
    assert (b*k2+l*LMAX)/L2<5
    assert k*LMAX/L2<2 and ahi*k2/L2<12

    def maxK(r,T):
        return a*M+(T-a)*(S[M-r+1]+r-1)

    candidates=[]
    exceptional=[]
    for v in range(1,5):
        for w in range(-1,12):
            P=v*p+w*q
            K=v*k+w*l
            if not 0<K<k2: continue
            low,high=gap((P,K))
            if high<=0 or low>=LMAX: continue
            assert 0<low<=high<LMAX
            r=max((r for r in range(1,M+1)
                   if low>F(r-1,DEN)+F(M-r+1,2**40-1)),default=0)
            assert r>0
            candidates.append((K,v,w,r))
            if K<=maxK(r,40):
                exceptional.append((P,K,v,w,r))
    assert len(candidates)==22
    assert exceptional==[(Q19[0],Q19[1],1,4,2)]
    P,K,_,_,_=exceptional[0]
    assert K>maxK(3,60)
    # Exactly two minima can lie up to 2^60. Each must be below Z.
    Z=F(17,10)*2**30
    assert gap((P,K))[0]>1/(Z-1)+F(1,DEN)+F(M-2,2**60-1)
    assert F(17,10)**5<2**4
    assert K>maxK(2,F(154,5))
    print("exact candidate table (K,v,w,forced small minima):")
    for row in sorted(candidates): print(*row)
    print("PASS large-minimum 5x+1 exclusion, m<=21")

if __name__=="__main__":
    if not __debug__: raise RuntimeError("use ordinary Python, not -O")
    main()
