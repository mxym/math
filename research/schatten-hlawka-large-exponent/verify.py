"""Supporting exact and numerical spot checks; not a proof of a universal inequality."""
from fractions import Fraction as Q
from itertools import product
import mpmath as m

def check_scalar():
    n=0
    grid=[Q(0),Q(1,5),Q(1,2),Q(1),Q(3,2),Q(4)]
    for k in range(2,16):
        for j in range(1,k):
            a,b=Q(j,k),Q(k-j,k)
            for x,y,sign in product(grid,grid,[-1,1]):
                u,v=x**k,sign*y**k
                B=a*u*u+b*v*v-sign*x**(2*j)*y**(2*(k-j))
                d=(u-v)**2
                assert a*b*d <= B <= 2*max(a,b)*d
                if sign==1:
                    assert min(a,b)*d <= B <= max(a,b)*d
                n+=1
    print(f"{n} exact signed rational instances of the scalar bound, with p=k/j.")

def check_multisummand():
    from itertools import combinations_with_replacement,combinations
    count=0
    for k in range(2,11):
        for v in combinations_with_replacement((-3,-2,-1,0,1,2,3),k):
            total=sum(map(abs,v))-abs(sum(v))
            pairs=sum(abs(x)+abs(y)-abs(x+y) for x,y in combinations(v,2))
            assert total<=pairs
            count+=1
    print(f"{count} exact integer finite-list checks of scalar Adamovic (all sorted lists, 2<=k<=10).")

def numerical(pp):
    p=m.mpf(pp);one=m.mpf(1);L=m.log(2);J=m.log(3);c=m.exp(J/p)
    # Direct objective of (2), evaluated via expm1 to avoid cancellation.
    def pieces(t):
        r=2*(abs(1-t)/2)**p
        am1=m.expm1(m.log(2+t**p)/p)
        bm2=2*m.expm1(m.log1p(r)/p)
        A=one+am1;B=2+bm2
        n=3*A-c*(2-t);d=6*am1-3*bm2
        ap=A*t**(p-1)/(2+t**p)
        bp=m.sign(t-1)*(abs(t-1)/2)**(p-1)*B/(one+r)
        return n,d,3*ap+c,6*ap-3*bp
    def f(t):
        n,d,dn,dd=pieces(t)
        return n/d
    def slope(t):
        n,d,dn,dd=pieces(t)
        return dn*d-n*dd
    lo,hi=m.mpf(".5"),one
    assert slope(lo)>0 and slope(hi)<0
    for _ in range(210):
        t=(hi+lo)/2
        if slope(t)>0:lo=t
        else:hi=t
    t=(lo+hi)/2
    K=f(t); approx=p/(3*L)-m.log(p)/(6*L)+(m.log(L)+2*L-J-1)/(6*L)
    # Verify against an independent difference of independently summed lp norms.
    X=[[-t,one,one],[one,-t,one],[one,one,-t]]
    def norm_idx(inds):return sum(abs(sum(X[i][col] for i in inds))**p for col in range(3))**(one/p)
    singles=sum(norm_idx((i,)) for i in range(3))
    df=2*singles-sum(norm_idx(ij) for ij in [(0,1),(1,2),(0,2)])
    ratio=(singles-norm_idx((0,1,2)))/df
    assert m.almosteq(K,ratio,rel_eps=m.mpf("1e-60"))
    for j in range(61):assert K+m.mpf("1e-45") >= f(m.mpf(".5")+j/m.mpf(40))
    err=(K-approx)*p/m.log(p)**2
    terr=(t-1+(m.log(p)-m.log(L))/p)*p**2/m.log(p)**2
    serr=(t**p-L/p)*p**2/m.log(p)
    assert max(abs(err),abs(terr),abs(serr))<3
    print(' '.join(m.nstr(x,14) for x in [p,t,K,err,terr,serr]))
if __name__=='__main__':
    m.mp.dps=83
    check_scalar()
    check_multisummand()
    print('p, scalar t*, R(t*), scaled K/t/s expansion remainders')
    for q in [256,'317.5',1024,4096,16384,65536,10**6,10**8]:
        numerical(q)
