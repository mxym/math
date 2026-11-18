"""Independent exact validation; SymPy 1.14; does not import the candidate selector."""
from itertools import combinations
from random import Random
from sympy import Matrix, diag, Rational as Q, zeros, I as ii, Symbol, expand, simplify, prod
rng=Random(73814)
def psd(A):
    # Exact symmetric/Hermitian semidefinite elimination, valid on singular inputs.
    while A.rows:
        d=A[0,0].expand(complex=True)
        assert d.is_real
        if d<0:return False
        if d==0:
            if any(A[0,i]!=0 for i in range(1,A.cols)):return False
            A=A[1:,1:]; continue
        A=(A[1:,1:]-A[1:,:1]*A[:1,1:]/d).applyfunc(lambda a:a.expand(complex=True))
    return True
def uncov(F,p,I):
    return F.H*diag(*[int(i in I)-a for i,a in enumerate(p)])*F
def dual():
    tests=good=bad=0
    for r,q in [(1,3),(2,3),(2,5),(3,5),(3,6),(3,7),(4,6),(4,7)]:
        for rep in range(4):
            while True:
                A=Matrix(q,r,lambda i,j:rng.randrange(-3,4))
                if rep==1:A[0,:]=A[1,:] # repeated direction; still full column rank
                if rep==3:A[0,:]=zeros(1,r)
                if A.rank()==r:break
            a=[rng.randint(1,14) for i in range(q)]; a[0]=10000 if rep%2 else 1
            p=[Q(x,sum(a)) for x in a]
            R=Matrix.hstack(*(A.T*diag(*p)).nullspace())
            assert R.cols==q-r
            for I in combinations(range(q),r):
                M=uncov(A,p,I)
                N=R.T*diag(*[(int(i not in I)-x)*x/(1-x) for i,x in enumerate(p)])*R
                assert psd(M)==psd(N)
                good+=int(psd(M)); bad+=int(not psd(M)); tests+=1
    print('dual equivalence:',tests,'candidate subsets;',good,'feasible;',bad,'infeasible')
def line():
    tests=good=cases=0
    for r,n in [(1,5),(2,7),(3,8),(4,9)]:
        for rep in range(5):
            x=[Q(2*i-3,1 if rep%2 else 1+i%3) for i in range(n)]
            if rep==1:x[-2:]=[x[0],x[1]] # repeated nodes, unequal weights
            if rep==2:x[1]=x[0]+Q(1,10**10)
            a=[rng.randint(1,9) for i in range(n)];a[0]=10**13 if rep==3 else 6
            if rep==4:a=[1]+[0]*(n-1) # limiting rank-deficient covariance
            p=[Q(v,sum(a)) for v in a]; w=[Q(rng.randint(1,10),rng.randint(1,10)) for i in x]
            V=Matrix([[v**k for k in range(r)] for v in x])
            val=False
            for I in combinations(range(n),r):
                if len({x[i] for i in I})<r:continue
                M=V.T*diag(*[b*(int(i in I)-p[i]) for i,b in enumerate(w)])*V
                ok=psd(M); val|=ok;good+=int(ok);tests+=1
            assert val;cases+=1
    print('line brute-force:',cases,'instances;',tests,'distinct-node candidate subsets;',good,'feasible')
def circle():
    t=Symbol('t');cases=0
    for r in (1,2,3,4):
        x=list(map(Q,[-5,-2,0,1,4,8]))
        C=Matrix(r,r,lambda j,k:expand((t-ii)**k*(t+ii)**(r-1-k)).coeff(t,j))
        assert C.det()!=0
        for u in x:
            z=(u-ii)/(u+ii); v=Matrix([[z**i for i in range(r)]]); a=Matrix([[u**i for i in range(r)]])
            assert (v.H*v-C.H*a.T*a*C/(1+u*u)**(r-1)).applyfunc(lambda e:e.expand(complex=True))==zeros(r)
            cases+=1
    print('Cayley transfer: exact per-observation Hermitian congruence',cases,'count')
def sharp():
    count=0
    for r in range(1,6):
        x=list(map(Q,range(r+1))); ms=[1+j%3 for j in range(r+1)]; n=sum(ms)
        u=[(1-Q(m,n))/r for m in ms]
        a=[1/(m*v*prod(s-t for t in x if s!=t)**2) for s,m,v in zip(x,ms,u)]
        V=Matrix([[s**k for k in range(r)] for s in x])
        for j in range(r+1):
            M=V.T*diag(*[w*(int(i!=j)-Q(m,n)) for i,(w,m) in enumerate(zip(a,ms))])*V
            assert psd(M) and M.rank()==r-1
            count+=1
    print('extremizers: all',count,'omitted-direction choices have exactly one zero eigenvalue')
if __name__=='__main__':dual();line();circle();sharp()
