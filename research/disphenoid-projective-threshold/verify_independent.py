#!/usr/bin/env python3
"""Independent angular maximization, exposed-face solve and Pauli traces."""
from itertools import product, combinations
import numpy as np

rng=np.random.default_rng(904)
S=np.asarray(((1,1,1),(1,-1,-1),(-1,1,-1),(-1,-1,1)),dtype=float)
pairs=list(combinations(range(3),2))
pauli=np.asarray([[[0,1],[1,0]],[[0,-1j],[1j,0]],[[1,0],[0,-1]]],dtype=complex)
I=np.eye(2)
psi=np.asarray([0,1,-1,0])/np.sqrt(2)
singlet=np.outer(psi,psi)
angles=np.linspace(0,np.pi/4,8193)
all_w=np.stack((np.cos(angles),np.sin(angles),np.sin(angles)),axis=1)

def support(r):
    order=np.flip(np.argsort(r))
    radius=r[order]
    j=np.argmax(np.sum(all_w*radius,axis=1))
    if j==len(angles)-1:
        w=np.ones(3)/np.sqrt(2)
    else:
        # A smooth angular maximizer; the grid locates the active face,
        # optimization along the arc is then an ordinary two-vector norm.
        angle=np.arctan2(radius[1]+radius[2],radius[0])
        angle=min(angle,np.pi/4)
        w=np.asarray([np.cos(angle),np.sin(angle),np.sin(angle)])
    opt=w@radius
    approx=all_w[j]@radius
    assert 0<=opt-approx+2e-14<=1e-8*max(1,opt)
    orig_order=np.zeros(3)
    orig_order[order]=w
    return opt,orig_order

def detector(u):
    if np.linalg.norm(u)<1e-15: return np.asarray([I/4]*4)
    rho=np.zeros((4,2,2),complex)
    G,w=support(np.abs(u))
    assert G<=1+1e-12
    atoms=[]
    for i,j in pairs:
        z=np.zeros(3)
        z[[i,j]]=w[[i,j]]
        if abs(np.linalg.norm(z)-1)<1e-12:
            atoms.append((z,3-i-j))
    # Reconstruct exposed-face mixture from a full linear system,
    # not the explicit rational case weights of the first checker.
    rows=np.vstack((np.asarray([z for z,k in atoms]).T,np.ones(len(atoms))))
    target=np.append(np.abs(u)/G,1)
    prob=np.linalg.lstsq(rows,target,rcond=None)[0]
    assert np.min(prob)>-1e-9 and np.max(np.abs(rows@prob-target))<1e-9
    signs=np.where(u>=0,1,-1)
    for p,(z,k) in zip(prob,atoms):
        for e in (-1,1):
            a,b=np.flatnonzero(S[:,k]==e)
            A=np.tensordot(z*signs*S[a],pauli,axes=1)
            rho[a]+=G*p*(I+A)/4
            rho[b]+=G*p*(I-A)/4
    return rho+(1-G)*I/4

def direct(A,B,rho):
    return np.asarray([[np.trace(rho@np.kron(a,b)).real
                        for b in B] for a in A])

def check_effects(A):
    assert np.max(np.abs(np.sum(A,axis=0)-I))<1e-10
    assert np.max(np.abs(np.trace(A,axis1=1,axis2=2)-.5))<1e-10
    assert np.min(np.linalg.eigvalsh(A))>=-1e-10

def fullcheck(C):
    r=np.sqrt(np.abs(C))
    A=detector(r)
    B=detector(-np.sign(C)*r)
    check_effects(A)
    check_effects(B)
    expected=(1+(S*C)@S.T)/16
    P=direct(A,B,singlet)
    assert np.max(np.abs(P-expected))<1e-9 and np.min(P)>=-1e-10
    assert np.max(np.abs(S.T@P@S-np.diag(C)))<1e-9
    return P

for i in range(192):
    r=rng.uniform(.01,1,3)**2
    r/=np.linalg.norm(r)
    G,w=support(r)
    if np.max(r)<np.sum(r)-np.max(r):
        expected=np.sum(r)/np.sqrt(2)
    else:
        z=np.max(r)
        expected=np.hypot(z,np.sum(r)-z)
    assert abs(expected-G)<1e-7
    r=r/G
    signs=rng.choice((-1,1),size=3)
    fullcheck(signs*r*r)
    fullcheck(.37*signs*r*r)
print("independent angular and exposed-face certificates: 192 boundary and 192 interior Born tables PASS")

def eff(u):
    R=[]
    for s in S:
        R.append((I+np.tensordot(s*u,pauli,axes=1))/4)
    return np.asarray(R)

Bell=np.asarray([[1,0,0,1],[1,0,0,-1],[0,1,1,0],[0,1,-1,0]])/np.sqrt(2)
for i in range(48):
    rho=Bell.T@np.diag(rng.dirichlet(np.ones(4)))@Bell
    r=rng.uniform(.2,1,3)
    r/=np.linalg.norm(r)
    T=np.asarray([[np.trace(rho@np.kron(a,b)).real for b in pauli] for a in pauli])
    assert np.max(np.abs(T-np.diag(np.diag(T))))<1e-12
    C=r*r*np.diag(T)/2  # half visibility via mixing white noise
    P=direct(eff(r),eff(r),(rho+np.eye(4)/4)/2)
    assert np.max(np.abs(fullcheck(C)-P))<1e-9
print("aligned Bell-diagonal noise: 48 directly generated probability tables PASS")

# Numerically cross-check the underlying witness on generic PS
# measurement pairs where P need not have uniform marginals.
def random_ps():
    E=np.zeros((4,2,2),complex)
    for p in rng.dirichlet(np.ones(5)):
        a,b=rng.integers(4,size=2)
        u=rng.normal(size=3)
        R=np.tensordot(u/np.linalg.norm(u),pauli,axes=1)
        E[a]+=p*(I+R)/2
        E[b]+=p*(I-R)/2
    return E

for i in range(160):
    G=rng.normal(size=(4,4))+1j*rng.normal(size=(4,4))
    rho=G@G.conj().T
    rho/=rho.trace().real
    weights=rng.uniform(.05,1,3)
    x=S*weights
    P=direct(random_ps(),random_ps(),rho)
    cov=x.T@(P-np.outer(P.sum(axis=1),P.sum(axis=0)))@x
    witness=np.sum(np.sqrt(np.linalg.svd(cov,compute_uv=False)))
    diameter=np.max(np.linalg.norm(x[:,None,:]-x[None,:,:],axis=-1))
    assert witness<=diameter/2+1e-9
print("generic two-qubit state and private PS witness stress: 160 trials PASS")

r=np.sqrt([.5,.25,.25])
o,w=support(r)
assert np.isclose(1-1/o**2,8*np.sqrt(2)-11)
print("RHB (1/2,1/4,1/4) example: exact critical noise = %.12f" % (1-1/o**2))

def one_ps(C):
    d=np.abs(C)
    coeff=d**(2/3)
    order=np.flip(np.argsort(coeff))
    weights=all_w**(2/3)
    grid=np.sum(weights*coeff[order],axis=1)
    k=np.argmax(grid)
    x=coeff[order][0]
    y=sum(coeff[order][1:])
    theta=min(np.arctan2(y**.75,x**.75),np.pi/4)
    w=np.zeros(3)
    w[order]=(np.cos(theta),np.sin(theta),np.sin(theta))
    F=coeff@(w**(2/3))
    assert abs(F-grid[k])<1e-8 and F>0
    a=coeff*(w**(-1/3))/F
    b=d/a
    assert abs(support(a)[0]-1)<1e-9
    assert abs(np.linalg.norm(b)-F**1.5)<1e-9
    return F**1.5,a,b

for i in range(144):
    q=rng.uniform(.01,1,3)**2
    q/=sum(q)
    G,_,_=one_ps(q)
    upper=1/G
    lower=1/support(np.sqrt(q))[0]**2
    assert 0<lower<upper<1
    signs=rng.choice((-1,1),size=3)
    for v in [(lower+upper)/2,upper]:
        C=v*q*signs
        J,a,b=one_ps(C)
        A=detector(a)
        B=eff(-signs*b)
        check_effects(A)
        check_effects(B)
        assert J<=1+1e-12
        P=direct(A,B,singlet)
        assert np.max(np.abs(P-(1+(S*C)@S.T)/16))<1e-9
        assert support(np.sqrt(np.abs(C)))[0]>1
    C=-(upper+1)*q/2
    assert np.min((1+(S*C)@S.T)/16)>0
    assert one_ps(C)[0]>1
print("one-PS direct factors: 144 exact-boundary, 144 two-PS exclusions, 144 one-PS exclusions PASS")
