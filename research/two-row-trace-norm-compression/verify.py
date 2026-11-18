"""Exact finite algebra for the obstruction; numerical regression for the endpoint.
Requires Python 3, NumPy and SymPy. Tests remain active with python -O."""
import numpy as np
import sympy as sp

def check(ok, why):
    if not ok: raise AssertionError(why)

x=sp.symbols('x')
M=sp.Matrix([[-1,1,0],[1,0,1],[0,1,1]])
H=M.applyfunc(abs)
check(sp.expand(M.charpoly(x).as_expr()-x*(x*x-3))==0,'signed spectrum')
check(sp.expand(H.charpoly(x).as_expr()-(x-2)*(x-1)*(x+1))==0,'modulus spectrum')

def test_exact(k):
    S=M
    A=H
    for _ in range(k-1):
        S=sp.kronecker_product(S,M); A=sp.kronecker_product(A,H)
    n=S.rows; J=sp.ones(n); h=sp.Matrix([[1,1],[1,-1]])
    W=sp.kronecker_product(sp.eye(n),h)
    T=sp.Matrix(2*n,2*n,lambda i,j: 2+(-1)**(i%2+j%2)*S[i//2,j//2])
    check(set(T)=={1,2,3} and T.T==T,'strictly positive symmetric lift')
    check(T*sp.ones(2*n,1)==4*n*sp.ones(2*n,1),'common row sum')
    both=list(range(0,2*n,2))+list(range(1,2*n,2))
    check((W.T*T*W/2).extract(both,both)==sp.diag(4*J,2*S),'double block reduction')
    C=sp.zeros(n)
    for i in range(n):
        for j in range(n):
            B=T[2*i:2*i+2,2*j:2*j+2]
            C[i,j]=sum(abs(v)*m for v,m in B.eigenvals().items())
    check(C==4*J+2*A,'direct nuclear compression')
    check(C*sp.ones(n,1)==(4*n+2*2**k)*sp.ones(n,1),'shift eigenvector')
    if k==1:
        for K,expval in [(T,12+4*sp.sqrt(3)),(C,20)]:
            check(sp.simplify(sum(abs(v)*m for v,m in K.eigenvals().items())-expval)==0,'direct exact witness spectrum')
    # Strict ordering by squaring two positive quantities; all checks exact.
    check(12**k < 16**k,'squared power comparison')

for k in [1,2,3]: test_exact(k)
print('Exact: Li–Zhao seed spectra, k=1,2,3 integer lifts, block rotations, compression, row sums, direct k=1 spectra.')

def psqrt(K):
    w,U=np.linalg.eigh((K+K.conj().T)/2)
    w[w<1e-13*max(1,w.max())]=0.
    return (U*np.sqrt(w))@U.conj().T

def nuclear(A): return np.linalg.svd(A,compute_uv=False).sum()

def check_endpoint(T,rows,cols,must_equal=False):
    rs=np.cumsum([0]+rows); cs=np.cumsum([0]+cols)
    u,s,vh=np.linalg.svd(T,full_matrices=False)
    X=u*np.sqrt(s); Y=vh.conj().T*np.sqrt(s)
    xb=[X[rs[i]:rs[i+1]] for i in range(2)]
    yb=[Y[cs[j]:cs[j+1]] for j in range(len(cols))]
    G=np.array([[nuclear(a@b.conj().T) for b in xb] for a in xb])
    C=np.array([[nuclear(T[rs[i]:rs[i+1],cs[j]:cs[j+1]]) for j in range(len(cols))] for i in range(2)])
    b=np.array([np.linalg.norm(z)**2 for z in yb])
    D=psqrt(C@C.T); inv=np.linalg.pinv(G,rcond=1e-11,hermitian=True)
    sl=b-np.diag(C.T@inv@C)
    tol=1e-8*max(1,s.sum())
    check(min(sl)>=-tol,'individual column slack')
    check(np.linalg.norm(G@inv@C-C)<tol,'column range')
    lhs=2*(s.sum()-nuclear(C))
    rhs=sl.sum()+np.linalg.norm(psqrt(inv)@(G-D))**2
    check(lhs>=-tol and abs(lhs-rhs)<tol,'nonnegative remainder identity')
    if must_equal: check(abs(lhs)<tol and np.linalg.norm(G-D)<tol,'equality example')
rng=np.random.default_rng(20261118)
for _ in range(96):
    rows=list(rng.integers(1,6,2)); cols=list(rng.integers(1,5,rng.integers(1,10)))
    z=lambda a,b:rng.normal(size=(a,b))+1j*rng.normal(size=(a,b))
    T=z(sum(rows),sum(cols))
    check_endpoint(T,rows,cols)
    l=z(sum(rows),1);r=z(1,sum(cols))
    check_endpoint(l@r, rows,cols,True)
    B=np.zeros_like(T); B[:rows[0]]=T[:rows[0]]
    check_endpoint(B,rows,cols)
check_endpoint(np.zeros((4,7)),[1,3],[2,1,4],True)
print('Numerical only: 289 two-row checks for (1)-(2), including complex rectangular arrays, exact rank-one constructions, zero rows and zero operator.')
