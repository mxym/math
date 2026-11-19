"""Unordered mask / assigned-bit enumeration in 67-bit binary hosts."""
from collections import Counter
from itertools import product
from math import comb,prod
A='01'*32
B='01'*16+'10'*16
HA={1:4,2:192,3:128,4:4096,6:4032,8:41664,65:2,128:64,129:2}
HB={1:10,2:372,3:189,4:5735,6:3908,8:37820,9:62,10:1,12:1953,34:4,65:3,66:60,67:2,68:62,99:2,128:1}
def require(z,m):
    if not z:raise ArithmeticError(m)
def put(x,i):
    return ((x>>i)<<(i+1))|(x% (1<<i))
def histogram(y):
    # Bit coordinates increase from the least significant end. All hosts
    # have the same known length, so leading zeroes cause no identifications.
    n=len(y);x=int(y,2);c=Counter()
    for i in range(n+1):
        z=put(x,i)
        for zi in (z,z+(1<<i)):
            for j in range(i+1,n+2):
                u=put(zi,j)
                for uj in (u,u+(1<<j)):
                    for k in range(j+1,n+3):
                        v=put(uj,k)
                        c[v]+=1;c[v+(1<<k)]+=1
    require(sum(c.values())==8*comb(n+3,3),'raw mask count')
    return dict(sorted(Counter(c.values()).items()))
def main():
    ha=histogram(A);hb=histogram(B)
    require(ha==HA and hb==HB,'histograms')
    require(sum(ha.values())==sum(hb.values())==50184,'support')
    require(sum(k*v for k,v in ha.items())==sum(k*v for k,v in hb.items())==383240,'mass')
    q_a=prod(k**(k*v) for k,v in ha.items())
    q_b=prod(k**(k*v) for k,v in hb.items())
    p=2**76566*43**258
    q=3**28089*5**75*11**4158*13**65*17**4352*67**134
    require(p*q_b==q*q_a,'prime ratio')
    require((q<<45)<p<(q<<46),'dyadic interval')
    print('m=64, transmitted length 67: supports 50184, masses 383240')
    print('A',ha);print('B',hb)
    print('Q(A)/Q(B)=2^76566*43^258/(3^28089*5^75*11^4158*13^65*17^4352*67^134)')
    print('integer 2^45 < Q(A)/Q(B) < 2^46 verified')
if __name__=='__main__':main()
