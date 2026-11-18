"""Independent exact checks for the cyclic-trace and averaged-word criteria. No third-party packages."""
from fractions import Fraction as F
from math import comb, lcm
from itertools import combinations, product
def must(ok,note):
    if not ok:raise ValueError(note)
def comps(n,k):
    for bars in combinations(range(1,n),k-1):
        end=(0,)+bars+(n,)
        yield tuple(end[i+1]-end[i] for i in range(k))
def two_minima(aa,bb):
    n,m=sum(aa),sum(bb);k=len(aa);D=lcm(n,m,2);a=[t*(D//n) for t in aa];b=[t*(D//m) for t in bb];H=D//2
    # Optimize J analytically given I. Bit I=selected high-eigenvalue left state.
    optimum=D
    for I in range(1<<k):
        def bit(j):return (I>>(j%k))&1
        Q=D-sum(a[i]*bit(i) for i in range(k))+sum(min(b[j],H*(bit(j)+bit(j+1))) for j in range(k))
        optimum=min(Q,optimum)
    # Independent shortest-path min-plus dynamic programming on alternating high/low states around the cycle.
    # state 1 incurs the small spectral eigenvalue; state 0 on both ends incurs the small-overlap cost.
    weight=[t for pair in zip(a,b) for t in pair]
    best=10*D
    for initial in (0,1):
        v=[10*D]*2;v[initial]=initial*weight[0]
        for z in weight[1:]:
            v=[min(v[prev]+int(prev==cur==0)*H for prev in (0,1))+cur*z for cur in (0,1)]
        best=min(best,min(v[prev]+int(prev==initial==0)*H for prev in (0,1)))
    must(best==optimum,'cut vs tropical cycle')
    return F(optimum,D)
ct=0;cs=0
for n,m in product(range(1,9),repeat=2):
    allgood=True
    for k in range(1,min(n,m)+1):
        for a in comps(n,k):
            for b in comps(m,k):
                d=two_minima(a,b);ct+=1
                allgood&=(d>=1)
                if k==2:
                    must((d>=1)==(abs(F(a[0],n)-F(1,2))+abs(F(b[0],m)-F(1,2))<=F(1,2)), 'diamond')
                    cs+=1
    must(allgood==(2*(n+m)>=n*m),'averaged threshold')
print('paired cyclic compositions:',ct,'four-run grid checks:',cs)

def ratio(a,b,D):
    # a,b integer numerators with common denominator D.
    # z=10^-6, t=z^(2D), so h=sqrt(t)=z^D and every t^exponent is rational.
    z=F(1,10**6);t=z**(2*D);hi=z**D;low=(1-hi)/2;swap2=(1-t)/2
    trace=0
    for states in product(range(2),repeat=2*len(a)):
        w=z**(2*sum((a[i//2] if not i%2 else b[i//2])*s for i,s in enumerate(states)))
        change=0
        for s,ss in zip(states,states[1:]+states[:1]):
            if s==ss:w*=hi if s==0 else low
            else:change+=1
        must(not change%2,'parity')
        trace+=w*swap2**(change//2)
    den=hi*hi+2*t*swap2+t*t*low*low
    return trace/den
# One-crossing strict outsider just 0.01 beyond the boundary; zero-crossing outsider; boundary.
R1=ratio((76,24),(75,25),100)
R2=ratio((7,1,2),(1,8,1),10)
R3=ratio((76,24),(74,26),100)
must(R1>10**10 and R2>10**55 and 0<R3<=1,'finite cut spectra')
print('3D one-crossing, zero-crossing and boundary explicit rational tests: PASS')

# Average words directly by integer-matrix recurrence with common dyadic denominator.
# A = Pp + t^m Pu, B=Pq+t^n Pv, multipliers 2*t^(-m/n) respectively.
def mm(A,B):return tuple(tuple(sum(A[i][s]*B[s][j] for s in range(3)) for j in range(3)) for i in range(3))
def add(A,B):return tuple(tuple(A[i][j]+B[i][j] for j in range(3)) for i in range(3))
def tr(A):return sum(A[i][i] for i in range(3))
Id=((1,0,0),(0,1,0),(0,0,1))
def powers(A,n):
    X=Id
    for j in range(n):X=mm(X,A)
    return X
for n,m in ((4,5),(3,7),(5,4),(4,4),(3,6),(2,9)):
    R=2**20
    A=((2*R**m,0,0),(0,1,-1),(0,-1,1))
    B=((1,-1,0),(-1,1,0),(0,0,2*R**n))
    tab={(0,0):Id}
    for i in range(n+1):
        for j in range(m+1):
            if i*j:tab[i,j]=add(mm(tab[i-1,j],A),mm(tab[i,j-1],B))
            elif i:tab[i,j]=mm(tab[i-1,j],A)
            elif j:tab[i,j]=mm(tab[i,j-1],B)
    avg=F(tr(tab[n,m]),comb(n+m,n)*tr(mm(powers(A,n),powers(B,m))))
    must((avg>1)==(2*(n+m)<n*m),'explicit average')
    print('average ratio floor',n,m,avg.numerator//avg.denominator)
