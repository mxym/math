"""Independent finite exact checks using SymPy. Not a numerical optimization/proof of universality."""
from itertools import product, combinations
from sympy import Matrix as M, Rational as Q, eye, zeros, diag, I, sqrt

def require(value, why):
    if not value:
        raise ArithmeticError(why)

def bases(t):
    j=M([[0,-1,1],[1,0,-1],[-1,1,0]])
    def cayley(z): return (eye(3)-z*j).inv()*(eye(3)+z*j)
    u=[eye(3),cayley((1-t)*(1-2*t)),cayley((1-t)*(6*t-1))]
    require(all(b.T*b==eye(3) and b.det()==1 for b in u), "bad SO3")
    return u
def trans(u):
    d=u[0].rows
    return [M.hstack(*(u[x][:,a] for a,x in enumerate(pattern))).det()
            for pattern in product(range(3), repeat=d)]
def sym(x,y): return (x*y.T+y*x.T)/2
def tensors(u):
    return [sym(u[0][:,a],u[x][:,a]) for a in range(3) for x in [1,2]]
def flatten(s):
    return M([s[i,j] for i in range(s.rows) for j in range(i+1)])
def coeffs(u): return M.hstack(*(flatten(s) for s in tensors(u)))
def gramcheck(u,L,admits_zero=False):
    for a in range(u[0].cols):
        V=M.hstack(*(b[:,a] for b in u))
        G=V.T*L*V
        for i,j in combinations(range(3),2):
            require(G[i,i]*G[j,j]>4*G[i,j]**2, 'off-diagonal dominance')
            if not admits_zero: require(G[i,j]!=0, 'orthogonal pair')
        H=[]
        for x in range(3):
            h=G.copy()
            for j in range(3):
                h[j,j]/=2
                h[x,j]=0
                h[j,x]=0
            others=[j for j in range(3) if j!=x]
            k=h.extract(others,others)
            require(k[0,0]>0 and k.det()>0 and h[:,x]==zeros(3,1),'factor exclusion')
            H.append(h)
        require(sum(H,zeros(3))==G and G.det()>0,'factor sum / Gram independence')

u0=bases(Q(0)); u1=bases(Q(1)); uh=bases(Q(1,2))
C=M([[0,0,1],[1,0,0],[0,1,0]])
require(u0==[eye(3),C,C**2] and uh==[eye(3),eye(3),C] and u1==[eye(3)]*3,'interpolation')
require(set(trans(u1))=={1} and abs(coeffs(uh).det())==Q(1,8),'variable endpoints')
print('PASS rational rotation identities at 0, 1/2, 1; six midpoint forms independent')

u=bases(Q(1,1000))
L=diag(1,2,3)/6
for L0 in (L,diag(1,4,9)/14,eye(3)/3):
    gramcheck(u,L0)
require(len(trans(u))==27 and all(trans(u)), '3d singular transversal')
f=coeffs(u); require(f.det()!=0,'six constraints fail')
w=f.inv()*flatten(eye(3))
require(sum((a*b for a,b in zip(w,tensors(u))),zeros(3))==eye(3),'dual certificate')
print('PASS 3d: 27 full-rank transversals, rank-six constraints, Gram exclusion at three spectra')

# 3d Schmidt support in ambient dimension five. Verify openness of both impossibilities
# by an explicit affirmative separation certificate for this example instead of using an SDP.
def rot(i,j,s):
    r=eye(5); c=(1-s*s)/(1+s*s); l=2*s/(1+s*s)
    r[i,i]=c; r[j,j]=c; r[i,j]=l; r[j,i]=-l
    return r
p=Q(1,10**9); o=rot(0,3,p)*rot(0,4,p)
U=[diag(b,eye(2))*o for b in u]
require(all(b.T*b==eye(5) for b in U),'5d bases')
for x in range(3):
    for a in (0,3,4):
        require(o[0,a]!=0 and U[x][:3,a]==o[0,a]*u[x][:,0],'exact posterior ray')
ds=trans(U);require(len(ds)==243 and all(ds),'5d transversal')
gramcheck(U,diag(L,zeros(2)))
W=sum((a*b for a,b in zip(w,tensors(U))),zeros(5))
for a in (3,4): W+=sym(U[0][:,a],U[1][:,a])
require(all(W[i,i]-sum(abs(W[i,j]) for j in range(5) if j!=i)>Q(1,2)
            for i in range(5)),'5d positive dual separation')
print('PASS rank-3 probe in dimension 5: all posterior rays and Gram factors, '
      '243 nonzero determinants, identifying-constraint combination exceeds I/2')

# Nonreal tensors ensure that conjugation in the marginal criterion is tested nontrivially:
# raw v_j stored as j-th column of A. R_{jk}=<v_k,v_j> so marginal = (A^*A)^T.
A=M([[1+I,2,1],[2-I,I,3*I]])
x=M([1-I,2*I,3]);y=M([2,1+I,I])
R=(A.H*A).T
lhs=((A*x.conjugate()).H*(A*y.conjugate()))[0].expand(complex=True)
rhs=(y.H*R*x)[0].expand(complex=True)
require(lhs==rhs and lhs!=lhs.conjugate(), 'conjugation orientation')
print('PASS complex purification/Gram orientation')
