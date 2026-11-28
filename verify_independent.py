#!/usr/bin/env python3
"""Independent full spectra of three perturbed pencils on B=16 and B=24."""
import numpy as np


def sign(A):
    a,V=np.linalg.eigh(A)
    assert np.all(a!=0.)
    return (V*np.sign(a))@V.T,a


def energy_matrix(S):
    n=len(S[0])
    return 2*len(S)*np.eye(n*n)-2*sum(np.kron(x,x.T) for x in S)


for k in (2,3):
    I=np.eye(k); L=np.eye(2*k)
    U=np.roll(I,1,axis=0)
    V=I.copy(); V[0,0]=-1
    X=np.array(((0,1),(1,0)))
    Z=np.diag((1,-1))
    def reflection(a):
        O=np.zeros_like(a)
        return np.block([[O,a],[a.T,O]])
    R=[np.kron(Z,I),np.kron(X,I),reflection(U),reflection(V)]
    n=4*len(L)
    V0=(np.eye(4)+np.ones((4,4)))/np.sqrt(7.)
    F=np.kron(np.linalg.inv(V0).T,L)
    B=F@F.T
    A=F@np.kron(np.diag((1,2,3,4)),L)@F.T
    E=F@np.block([[R[i] if i==j else np.zeros_like(L) for j in range(4)]for i in range(4)])@F.T
    # Construct ideal signs by spectral projection, not the rotation formula.
    T=[]; Q=[]
    for i in range(4):
        la,vs=np.linalg.eigh(A-(i+1)*B)
        q=vs[:,abs(la)<1e-9]
        T.append((vs*np.where(abs(la)>1e-9,np.sign(la),0))@vs.T)
        Q.append(q@q.T)
        assert len(la[abs(la)<1e-9])==2*k
    J=[]
    for i in range(4):
        J.extend([T[i]+Q[i],T[i]+np.kron(np.outer(V0[:,i],V0[:,i]),R[i]),T[i]-Q[i]])
    assert all(np.max(abs(j@j-np.eye(n)))<1e-12 for j in J)
    eig=np.linalg.eigvalsh(energy_matrix(J))
    assert abs(eig[0])<1e-10 and eig[1]>1e-3
    # Negative control: duplicating the nontrivial unitary yields a nonscalar
    # commutant for the ideal sign system.
    Jbad=J.copy()
    Jbad[10]=T[3]+np.kron(np.outer(V0[:,3],V0[:,3]),R[2])
    assert abs(np.linalg.eigvalsh(energy_matrix(Jbad))[1])<1e-10
    old=100.
    for eps in (1e-3,1e-4,1e-5):
        A1=A+eps*E
        R0=B/np.trace(B); R1=A1/np.trace(A1)
        assert np.linalg.eigvalsh(R0)[0]>0 and np.linalg.eigvalsh(R1)[0]>0
        S=[]; min_scaled=100.
        for i in range(4):
            for f in (-2,0,2):
                lam=(i+1)+eps*f
                D=A1-lam*B
                a,V1=sign(D)
                expected=(3-i)*2*k+{-2:2*k,0:k,2:0}[f]
                assert np.count_nonzero(V1>0)==expected
                min_scaled=min(min_scaled, min(abs(V1))/eps)
                assert np.max(abs(a@a-np.eye(n)))<1e-12
                S.append(a)
        assert min_scaled >= .28-1e-8
        err=max(np.max(abs(np.linalg.eigvalsh(s-j))) for s,j in zip(S,J))
        assert err<old*.15
        old=err
        eig=np.linalg.eigvalsh(energy_matrix(S))
        assert abs(eig[0])<1e-10 and eig[1]>1e-3
        # Test witness deficits for a nonunital, rank-one reset channel.
        t=np.arange(1,n+1,dtype=float); t=t/np.linalg.norm(t)
        Reset=np.outer(t,t)
        for i,s in enumerate(S):
            lam=(i//3+1)+eps*((-2,0,2)[i%3])
            t0=lam*np.trace(B)/np.trace(A1)
            Delta=R1-t0*R0
            a=np.trace(s@(Delta-np.trace(Delta)*Reset))
            adj=np.trace(s@Reset)*np.eye(n)
            qq=np.eye(n)-(s@adj+adj@s)/2
            va=np.linalg.eigvalsh(Delta)
            assert abs(a-np.trace((s@Delta)@qq))<2e-12
            assert a>=min(abs(va))*np.trace(qq)-2e-12
        print(f"B={n:2} eps={eps:.0e}: {len(S)} signs, min gap/eps={min_scaled:.6f}, "
              f"max sign error/eps={err/eps:.6f}, traceless gap={eig[1]:.6f}")
print("finite spectral controls: 72 signed pencils, 72 nonunital deficits, 2 repeated-unitary failures")
