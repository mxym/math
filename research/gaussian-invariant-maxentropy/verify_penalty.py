"""Independent projected-precision tests and two small direct penalty optimizations."""
from itertools import product
from math import exp, pi, sqrt
import numpy as np
import sympy as sym
from scipy.integrate import quad
from scipy.linalg import null_space
from scipy.optimize import brentq, root
from scipy.stats import norm

def plane_leading(B,V):
    n,r=V.shape
    K=null_space(B.T)
    L=null_space(K.T)
    C=K.T@(V@V.T)@K
    Ji=L.T@B@B.T@L
    CI=np.linalg.inv(C)
    k=L.shape[1]
    As=[]
    a0=[]
    for i in range(r):
        for j in range(i,r):
            X=np.zeros((r,r))
            X[i,j]=X[j,i]=1
            As.append(np.diag(K@X@K.T))
            a0.append(np.trace(CI@X))
    A=np.array(As).T
    g=np.linalg.lstsq(A.T,np.array(a0),rcond=None)[0]
    assert np.max(np.abs(K.T@np.diag(g)@K-CI))<3e-10
    cross_basis=np.eye(r*k).reshape((r*k,r,k))
    T=np.array([2*np.diag(K@z@L.T) for z in cross_basis]).T
    Vperp=null_space(A.T)
    W=null_space(Vperp.T@T) if Vperp.shape[1] else np.eye(r*k)
    Ebas=(W.T@cross_basis.reshape((r*k,r*k))).reshape((-1,r,k))
    def ip(x,y): return np.trace(Ji@x.T@CI@y)
    cross=K.T@np.diag(g)@L
    M=np.array([[ip(x,y) for y in Ebas] for x in Ebas])
    ell=np.array([-2*np.sum(cross*x) for x in Ebas])
    coef=np.linalg.solve(M,ell/2)
    E=np.einsum('i,ijk->jk',coef,Ebas)
    return ip(E,E),K,L

def exact_angles(B,V):
    n=V.rows
    W=V.T*V
    G=V*W.inv()**2*V.T
    BB=B*B.T
    R=V*V.T
    J=BB.multiply_elementwise(R)
    ell=sym.Matrix([2*(sym.Matrix([[-V[i,1],V[i,0]]])*(G*V)[i,:].T)[0] for i in range(n)])
    assert J*sym.ones(n,1)==sym.zeros(n,1) and sum(ell)==0
    h=sym.zeros(n,1)
    h[1:n,0]=J[1:n,1:n].inv()*ell[1:n,0]/2
    assert 2*J*h==ell
    c=(h.T*J*h)[0]
    assert c>0 and (ell.T*h)[0]==2*c
    return c

def direct_penalty(B,V,tau,K):
    n=len(V)
    th=np.arctan2(V[:,1],V[:,0])
    BB=B@B.T
    def terms(delta):
        theta=th+np.r_[0.,delta]
        W=np.column_stack((np.cos(theta),np.sin(theta)))
        tangent=np.column_stack((-np.sin(theta),np.cos(theta)))
        R=W@W.T
        C=K.T@R@K
        inv=np.linalg.inv(C)
        H=BB-tau*K@inv@K.T
        M=H@W
        d=2*np.sum(M*tangent,axis=1)
        return d,H,M,W,R,C
    ans=root(lambda a:terms(a)[0][1:],np.zeros(n-1),tol=1e-10)
    d,H,M,W,R,C=terms(ans.x)
    assert np.max(np.abs(d))<2e-9
    # Small-tau global-eigenvalue witness: complementarity with the
    # rank-two Gram optimum plus positive eigenvalues on its complement.
    S=H-np.diag(np.sum(M*W,axis=1))
    assert np.linalg.norm(S@W)<3e-9
    spectrum=np.linalg.eigvalsh(S)
    assert np.max(np.abs(spectrum[:2]))<3e-9 and np.min(spectrum[2:])>.1
    v=np.sum((B.T@W)**2)
    loggap=np.linalg.slogdet(C)[1]-np.linalg.slogdet(K.T@V@V.T@K)[1]
    return v,loggap

def commuter():
    t=2*pi*np.arange(5)/5
    V=np.column_stack((np.cos(t),np.sin(t)))
    B=null_space(V.T)
    K=null_space(B.T)
    P=K@K.T
    p=np.diag(P)
    S=np.diag(p)
    assert np.allclose(P@S,S@P,atol=2e-12) and np.allclose(p,2/5)
    assert np.allclose(P@np.diag(1/p)@P,V@V.T,atol=2e-10)
    # Independent random correlation matrices test the first-order
    # exact optimum inequality and residual sign.
    rng=np.random.default_rng(77)
    for _ in range(64):
        A=rng.normal(size=(5,5))
        A/=np.linalg.norm(A,axis=1)[:,None]
        R=A@A.T
        O=V@V.T
        grad=K@np.linalg.inv(K.T@O@K)@K.T
        want=-np.trace(S@(np.eye(5)-P)@R)
        assert abs(np.trace(grad@(R-O))-want)<2e-10 and want<0
        assert np.linalg.slogdet(K.T@R@K)[1]<np.linalg.slogdet(K.T@O@K)[1]
    print("commuting non-simplex projector: 64 independent correlation and dual checks PASS")

def asymmetric():
    V=sym.Matrix([[1,0],[0,1],[sym.Rational(3,5),sym.Rational(4,5)],
                  [sym.Rational(5,13),-sym.Rational(12,13)]])
    B=sym.Matrix([[-3,-5],[-4,12],[5,0],[0,13]])
    assert V.T*B==sym.zeros(2)
    exact=exact_angles(B,V)
    b,v=[np.array(T.tolist(),dtype=float) for T in (B,V)]
    P=v@np.linalg.inv(v.T@v)@v.T
    S=np.diag(np.diag(P))
    assert np.linalg.norm(P@S-S@P)>1e-3
    both,K,L=plane_leading(b,v)
    assert abs(both-float(exact))<2e-11
    for tau in [.01,.003,.001]:
        a,g=direct_penalty(b,v,tau,K)
        assert abs(a/tau**2-both)<.002*both and abs(g/tau-2*both)<.003*both
    print("noncommuting rank-two/two-constraint case: exact tangent coefficient %s and direct penalty PASS" % exact)

def scalar_penalty():
    for strength in [1,2,3]:
        target=1/(8*strength**2)
        for tau in [.01,.003,.001]:
            z=brentq(lambda z:4*strength**2*(z-1)-tau*(-2*z/(2-z*z)+2/(1+z)),.9,1.1,xtol=1e-15)
            v=2*strength**2*(z-1)**2
            assert abs(v/tau**2-target)<.04*target
    b=np.array([[sqrt(2)],[1.],[1.]])
    # R0 precisely u=1 from the explicit 3-by-3 graph matrix.
    V=np.array([[-1/sqrt(2),-1/sqrt(2)],[1,0],[0,1]])
    c,_,_=plane_leading(b,V)
    assert abs(c-.125)<5e-13
    print("independent scalar penalty: coefficient 1/8 and scale law 1/(8*a^2) PASS")

def privacy_profile():
    for a,e in product([.2,.7,1.4,3.2],[0.,.1,.6,1.3,2.]):
        cut=a/2-e/a
        val=quad(lambda x:norm.pdf(x)-exp(e)*norm.pdf(x-a),-np.inf,cut,
                 epsabs=2e-12,epsrel=2e-12)[0]
        exact=norm.cdf(cut)-exp(e)*norm.cdf(cut-a)
        assert abs(val-exact)<1e-11 and exact>=0
        assert exact<=norm.cdf(cut)+1e-12
    print("Gaussian support-coordinate calibration vs independent quadrature: 20 pairs PASS")

if __name__=='__main__':
    commuter()
    asymmetric()
    scalar_penalty()
    privacy_profile()
