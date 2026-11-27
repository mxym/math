"""Independent complex-matrix replay (does not import the label checker)."""
from itertools import product
import numpy as np

TOL=3e-8

def words(p,n):
    return list(product(range(p),repeat=n))

def powers(M,p):
    out=[np.eye(len(M),dtype=complex)]
    for _ in range(p-1): out.append(out[-1]@M)
    assert np.allclose(out[-1]@M,out[0],atol=TOL)
    return out

def pauli(w,p):
    omega=np.exp(2j*np.pi/p)
    z=np.diag(omega**np.arange(p))
    x=np.roll(np.eye(p),1,axis=0)
    u=np.ones((1,1),dtype=complex)
    for a,b in zip(w[0::2],w[1::2]):
        v=np.linalg.matrix_power(x,int(a))@np.linalg.matrix_power(z,int(b))
        if p==2 and a*b: v=1j*v
        u=np.kron(u,v)
    return u

def monomials(gens,p,ws):
    P=[powers(g,p) for g in gens]
    out={}
    for w in ws:
        v=P[0][w[0]]
        for i in range(1,len(w)):
            if w[i]: v=v@P[i][w[i]]
        out[w]=v
    return out

def fix_order(M,p):
    Mp=np.linalg.matrix_power(M,p)
    scalar=np.trace(Mp)/len(M)
    assert abs(abs(scalar)-1)<TOL and np.allclose(Mp,scalar*np.eye(len(M)),atol=TOL)
    return np.exp(-1j*np.angle(scalar)/p)*M

def direct_profile(p,m,images,expected_r,seed):
    rng=np.random.default_rng(seed)
    n=2*m
    d=p**m
    d2=d*d
    W=words(p,n)
    iw=np.eye(n,dtype=int)
    J=np.kron(np.eye(m,dtype=int),np.array([[0,-1],[1,0]]))
    images=np.asarray(images,dtype=int)
    assert len({tuple((np.array(w)@images)%p) for w in W})==d2
    D=(images@J@images.T-J)%p
    r=expected_r
    q=n-r
    assert sum(not np.any(np.array(w)@D%p) for w in W)==p**(n-2*r)
    # Independent graph embedding: a(v)=(v,Tv), using grouped x,z coordinates.
    # Then Omega_A(a(v),a(w))=v^T(T^T-T)w=-v^T D w.
    T=np.triu(D,k=1)
    def a(w):
        return np.stack((w,T@w%p),axis=-1).ravel()
    assert len({tuple(a(np.array(w))) for w in W})==d2
    B=[pauli(w,p) for w in images]
    U=[pauli(w,p) for w in iw]
    A=[pauli(a(w),p) for w in iw]
    HBasis=[np.kron(u.conj(),b) for u,b in zip(U,B)]
    Ah=monomials(A,p,W)
    Hh=monomials(HBasis,p,W)
    dA=len(A[0])
    for i in range(n):
        for j in range(i+1,n):
            X,Y=HBasis[i]@HBasis[j],HBasis[j]@HBasis[i]
            phase=np.trace(X@Y.conj().T)/d2
            assert abs(abs(phase)-1)<TOL and np.allclose(X,phase*Y,atol=TOL)
            assert np.allclose(phase*A[i]@A[j],A[j]@A[i],atol=TOL)
    identity=np.eye(d2,dtype=complex)
    def conditional(E):
        return sum(Hh[w]*np.trace(E@Ah[w]) for w in W)/(d2*dA)
    assert np.allclose(conditional(np.eye(dA)),identity/d2,atol=TOL)
    # An arbitrary (non-Pauli) three-outcome POVM. Verify each coarse effect
    # gives positive weight, the two pointwise upper bounds, and normalization.
    rands=[rng.normal(size=(dA,dA))+1j*rng.normal(size=(dA,dA)) for _ in range(3)]
    positives=[M@M.conj().T for M in rands]
    val,vec=np.linalg.eigh(sum(positives))
    inv=(vec/np.sqrt(val))@vec.conj().T
    effects=[inv@P@inv for P in positives]
    sigmas=[conditional(E) for E in effects]
    assert np.allclose(sum(sigmas),identity/d2,atol=TOL)
    for sig in sigmas:
        assert np.allclose(sig,sig.conj().T,atol=TOL)
        lam=np.linalg.eigvalsh(sig)
        pr=np.trace(sig).real
        assert lam[0]>=-TOL and lam[-1]<=min(pr*p**(-r),1/d2)+TOL

    # Construct a maximal isotropic basis by explicitly growing its span.
    S={(0,)*n}
    K=[]
    for w in W:
        if w in S or any(np.array(w)@D@np.array(v)%p for v in K): continue
        K.append(w)
        S={tuple((np.array(u)+i*np.array(w))%p) for i in range(p) for u in S}
    assert len(K)==q and len(S)==p**q
    HK=[]
    AK=[]
    for w in K:
        M=fix_order(Hh[w],p)
        c=np.trace(M@Hh[w].conj().T)/d2
        HK.append(M)
        AK.append(Ah[w]/c)
    root=np.exp(2j*np.pi/p)
    def all_eigenprojs(gens):
        return [[sum(root**(-j*k)*P for k,P in enumerate(powers(M,p)))/p
                 for j in range(p)] for M in gens]
    BP=all_eigenprojs(HK)
    AP=all_eigenprojs(AK)
    units=words(p,q)
    Q={}
    for h in units:
        E=np.eye(dA,dtype=complex)
        P=identity.copy()
        for i,c in enumerate(h):
            E=E@AP[i][-c%p]
            P=P@BP[i][c]
        sig=conditional(E)
        assert np.trace(E).real/dA>0
        assert abs(np.trace(E).real/dA-p**(-q))<TOL
        assert abs(np.trace(P).real-p**r)<TOL and np.allclose(P@P,P,atol=TOL)
        assert np.allclose(sig,P/d2,atol=TOL)
        Q[h]=P
    assert np.allclose(sum(Q.values()),identity,atol=TOL)

    # Independently find an actual unitary intertwiner on the chosen subspace.
    eye=np.eye(d)
    rows=[]
    for w in K:
        b=pauli((np.array(w)@images)%p,p)
        u=pauli(w,p)
        rows.append(np.kron(b.T,eye)-np.kron(eye,u))
    _, sval, VH=np.linalg.svd(np.concatenate(rows),full_matrices=False)
    null=VH.conj().T[:,sval<TOL]
    assert null.shape[1]>=1
    M=(null@(rng.normal(size=null.shape[1])+1j*rng.normal(size=null.shape[1]))).reshape((d,d),order='F')
    u,s,vh=np.linalg.svd(M)
    assert min(s)>TOL
    decoder=u@vh
    for w in K:
        b=pauli((np.array(w)@images)%p,p)
        assert np.allclose(decoder@b@decoder.conj().T,pauli(w,p),atol=TOL)
    phi=eye.reshape(-1)/np.sqrt(d)
    base=np.kron(eye,decoder.conj().T)@phi
    bells={}
    for w in W:
        vector=np.kron(eye,pauli(w,p))@base
        hits=[h for h,P in Q.items() if abs(np.vdot(vector,P@vector)-1)<TOL]
        assert len(hits)==1
        bells[hits[0]]=vector
    assert len(bells)==p**q
    for L in range(1,p**q+2):
        G=min(L,p**q)
        groups=[units[i::G] for i in range(G)]
        fidelity=0.
        for group in groups:
            bell=bells[group[0]]
            # Matrix overlap of the grouped, unnormalized physical state.
            f=np.vdot(bell,sum(Q[h] for h in group)@bell).real
            assert abs(f-1)<TOL
            fidelity+=f/d2
        assert abs(fidelity-min(p**(-r),L/d2))<TOL
    if r:
        # Negative control: no Bell decoder can accept every sector as perfect;
        # measuring then correcting along the decoder gives conditional p^-r.
        f0=max(np.vdot(base,Q[h]@base).real for h in Q)/p**r
        assert abs(f0-p**(-r))<TOL and f0<1-TOL
    print("matrix p=%d m=%d r=%d: arbitrary 3-effect POVM, %d Bell-labelled sectors, %d budgets PASS" %
          (p,m,r,p**q,p**q+1))

def main():
    direct_profile(2,1,np.eye(2,dtype=int),0,22)
    direct_profile(3,1,np.eye(2,dtype=int),0,33)
    direct_profile(3,1,np.diag([2,1]),1,34)
    B=np.eye(4,dtype=int)
    B[0,2]=1
    direct_profile(2,2,B,1,42)
    direct_profile(3,2,np.diag([2,1,2,1]),2,43)
    direct_profile(5,1,np.diag([2,1]),1,55)
    print("PASS independent complex-matrix checker and imperfect-scheme negative controls")

if __name__=='__main__': main()
