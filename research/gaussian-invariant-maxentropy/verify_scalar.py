"""Scalar construction, feasibility and optimality check; direct numerical max-det cross-checks."""
import numpy as np
from scipy.linalg import null_space
from scipy.optimize import brentq, minimize

def explicit(b):
    nz=np.flatnonzero(b)
    if not len(nz): return 'empty',np.eye(len(b)),None
    lead=nz[np.argmax(np.abs(b[nz]))]
    others=nz[nz!=lead]
    c=b[others]/b[lead]
    mass=np.abs(c).sum()
    if mass<1-2e-13: return 'unbalanced',None,None
    R=np.eye(len(b))
    active=np.r_[lead,others]
    if abs(mass-1)<2e-13:
        v=np.r_[-1,np.sign(c)]
        R[np.ix_(active,active)]=np.outer(v,v)
        return 'saturated',R,None
    w=c*c
    def a(u): return np.sqrt(1-w+w*u*u)
    def ratio(u): return (w*(1+u)/(1+a(u))).sum()
    if ratio(0)>=1-2e-14:
        u=0 if abs(ratio(0)-1)<2e-14 else brentq(lambda u:1-u+sum(1-a(u))-2,0,1,xtol=3e-15)
        x=(1-u)/2
        branch='join' if u==0 else 'all-minus'
    else:
        hi=1.
        while ratio(hi)<1: hi*=2
        u=brentq(lambda u:ratio(u)-1,0,hi,xtol=3e-15)
        x=(1+u)/2
        branch='plus-at-one' if abs(u-1)<1e-12 else ('plus-below-one' if u<1 else 'plus-above-one')
    s=(1-u*u)/4
    d=2/(1+a(u))
    C=np.diag(d)-s*np.outer(d*c,d*c)
    V=np.vstack((-c,np.eye(len(c))))
    R[np.ix_(active,active)]=V@C@V.T
    assert np.allclose(np.diag(C),1,atol=3e-10)
    assert abs(c@C@c-1)<3e-10
    assert np.linalg.eigvalsh(C)[0]>0
    assert np.allclose(np.linalg.inv(C),np.diag(1/d)+(s/x)*np.outer(c,c),atol=3e-8)
    assert abs(np.linalg.det(C)-x*np.prod(d))<2e-8
    return branch,R,(C,c)

def independent_det_search(C,c,rng):
    # No square-root, branch, multiplier or ratio identity is used in the
    # search; solve the affine constraints directly in free entries.
    k=len(c)
    i,j=np.triu_indices(k,1)
    a=2*c[i]*c[j]
    target=1-c@c
    center=target*a/(a@a)
    N=null_space(a[None,:])
    if not N.shape[1]:
        assert np.allclose(C[i,j],center,atol=3e-8)
        return
    x0=N.T@(C[i,j]-center)
    # Start at a reproducibly displaced feasible positive-definite point.
    step=rng.normal(size=len(x0))
    def form(x):
        R=np.eye(k)
        R[i,j]=R[j,i]=center+N@x
        return R
    t=.08
    while np.linalg.eigvalsh(form(x0+t*step))[0]<.05*np.linalg.eigvalsh(C)[0]:
        t/=2
    z0=x0+t*step
    assert np.linalg.norm(z0-x0)>0
    def fun(x):
        M=form(x)
        e=np.linalg.eigvalsh(M)
        if e[0]<=0: return 1e5-1e5*e[0]
        return -sum(np.log(e))
    def jac(x):
        M=form(x)
        e,V=np.linalg.eigh(M)
        if e[0]<=0: return -1e5*(N.T@(2*V[i,0]*V[j,0]))
        T=(V/e)@V.T
        return -2*N.T@T[i,j]
    ans=minimize(fun,z0,jac=jac,method='BFGS',options={'gtol':8e-10,'maxiter':500})
    assert abs(fun(ans.x)-fun(x0))<3e-8 and np.max(np.abs(form(ans.x)-C))<5e-6,(ans.message, C, form(ans.x))

def profiles():
    forced=[
        ('empty',[0,0,0]),
        ('unbalanced',[3,-1,1,0]),
        ('saturated',[2,-1,1,0]),
        ('saturated',[-2,2,0,0]),
        ('all-minus',[1,1,1,0]),
        ('all-minus',[3,-3,1,2,0]),
        ('join',[2,np.sqrt(3),np.sqrt(3)]),
        ('plus-below-one',[1,-.8,.7,0]),
        ('plus-at-one',[np.sqrt(2),1,-1]),
        ('plus-above-one',[1,.6,.5]),
        ('plus-above-one',[-1,.7,-.30001,0])]
    rng=np.random.default_rng(1697)
    checks=0
    def check_r(b,R,data):
        if R is None: return
        assert np.max(np.abs(np.diag(R)-1))<3e-9
        assert np.linalg.norm(R@b)<3e-9*max(1,np.linalg.norm(b))
        assert np.linalg.eigvalsh(R)[0]>-2e-10
        if data:
            C,c=data
            K=null_space(b[None,:])
            assert np.linalg.eigvalsh(K.T@R@K)[0]>0
            independent_det_search(C,c,rng)
    for expected, vals in forced:
        b=np.array(vals,dtype=float)
        kind,R,data=explicit(b)
        assert kind==expected,(kind,expected,b)
        check_r(b,R,data)
        checks+=int(data is not None)
    for m in range(3,11):
        for _ in range(16):
            vals=rng.uniform(.15,1.,size=m)
            vals*=rng.choice([-1,1],size=m)
            if 2*max(abs(vals))>=sum(abs(vals)): continue
            kind,R,data=explicit(vals)
            assert data is not None
            check_r(vals,R,data)
            checks+=1
    print("scalar roots: all five strict-root branches, both feasible degenerate cases, and infeasible control PASS")
    print("strict cases with independent free-affine log-det searches or unique affine point:",checks,"PASS")
    for n in range(2,9):
        b=np.ones(n)
        kind,R,_=explicit(b)
        want=n/(n-1)*np.eye(n)-np.ones((n,n))/(n-1)
        assert np.allclose(R,want,atol=3e-9)
    # Weighted laminar sets {{0,1,2,3,4,5,6},{0,1,2},{3,4,5}},
    # with weight zero on 6. Distinct fixed scales change both active problems.
    A=np.array([[1,-1,1,1,1,-1,0],[1,-1,1,0,0,0,0],[0,0,0,1,1,-1,0]],dtype=float)
    D=np.diag([.9,.8,1.,.5,.8,.65,2.])
    B=D@A.T
    R=np.eye(7)
    for ids in [slice(0,3),slice(3,6)]:
        _,R[ids,ids],_=explicit(B[ids,0])
    assert np.max(np.abs(B.T@R@B))<3e-9
    assert np.sum(np.linalg.eigvalsh(R)>1e-8)==5
    print("equal weights n=2..8 and heterogeneous laminar reduction PASS")

if __name__=='__main__':
    profiles()
