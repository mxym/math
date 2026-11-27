"""Independent array transcript, normalized-kernel, and entropy-tail checks."""
from math import acos, cos, e, log, pi
from itertools import product
import numpy as np

def char(n):
    return np.array([[1 if (x&y).bit_count()%2==0 else -1
                      for y in range(2**n)] for x in range(2**n)],dtype=float)

def check_shapes():
    rng=np.random.default_rng(860132)
    for _ in range(60):
        q=7
        prior=rng.dirichlet(np.array([.3,.6,.7,.9,1.,1.3,1.5]))
        A0=rng.dirichlet(np.ones(5)*.35,size=(3,q))
        A1=rng.dirichlet(np.ones(5)*.35,size=(3,q))
        B=rng.dirichlet(np.ones(8)*.40,size=(4,q))
        P=(A0+A1)/2
        UA=np.einsum('r,xra->xa',prior,P)
        UB=np.einsum('r,yrb->yb',prior,B)
        direct=np.abs(np.einsum('r,xra,yrb->xyab',prior,(A0-A1)/2,B)).sum(axis=(2,3))
        for locals_,marg in ((P,UA),(B,UB)):
            J=prior[None,:,None]*locals_
            M=prior[None,:,None]*marg[:,None,:]
            info=(J*np.log2(J/M)).sum(axis=(1,2))
            assert min(info)>=-1e-12
            for K in [1.05,1.7,2.2,5.0,10.0]:
                tail=np.maximum(J-K*M,0).sum(axis=(1,2))
                prob=np.where(J>K*M,J,0).sum(axis=(1,2))
                assert np.all(tail<=prob+1e-12)
                assert np.all(prob<=(info+1/(e*log(2)))/log(K,2)+1e-12)
        # Direct seed-matrix restriction followed by clipping.
        take=np.flatnonzero(prior>=.07)
        missing=1-sum(prior[take])
        K=1.45
        AA=(A0-A1)/2
        aclip=np.minimum(1,K*UA[:,None,:]/P)
        bclip=np.minimum(1,K*UB[:,None,:]/B)
        truncated=np.abs(np.einsum('r,xra,yrb->xyab',prior[take],AA[:,take],B[:,take])).sum(axis=(2,3))
        clipped_a=np.abs(np.einsum('r,xra,yrb->xyab',prior[take],(AA*aclip)[:,take],B[:,take])).sum(axis=(2,3))
        clipped_b=np.abs(np.einsum('r,xra,yrb->xyab',prior[take],AA[:,take],(B*bclip)[:,take])).sum(axis=(2,3))
        assert np.all(np.abs(truncated-direct)<=missing+1e-12)
        ha=np.einsum('r,xra->x',prior,np.maximum(P-K*UA[:,None,:],0))
        hb=np.einsum('r,yrb->y',prior,np.maximum(B-K*UB[:,None,:],0))
        assert np.all(np.abs(clipped_a-truncated)<=ha[:,None]+1e-12)
        assert np.all(np.abs(clipped_b-truncated)<=hb[None,:]+1e-12)
    print("direct array transcripts and KL/hockey-stick/tail constants: 60 channel systems PASS")

def cheb_order(m,z):
    u=np.arccos(np.clip(z,-1,1))
    y=np.full_like(u,2/pi,dtype=float)
    for j in range(1,m+1):
        y+=4/pi*((-1)**(j-1)/(4*j*j-1))*np.cos(2*j*u)
    return y

def check_hadamard():
    for n in range(1,9):
        H=char(n)
        N=len(H)
        assert np.array_equal(H@H.T,N*np.eye(N))
        rng=np.random.default_rng(n)
        # Rank certificate sanity on rectangular row subsets and PSD gram.
        inds=sorted(rng.choice(N,size=N//2+1,replace=False))
        R=H[inds]
        assert np.array_equal(R@R.T,N*np.eye(len(R)))
    for m in (1,2,4,9,25):
        z=np.linspace(-1,1,20001)
        assert np.max(np.abs(cheb_order(m,z)-np.abs(z)))<=2/(pi*(2*m+1))+1e-12
    print("Hadamard rectangular identities n=1..8 and 100005 independent Chebyshev evaluations PASS")

def check_noisy_construction(n):
    N=1<<n
    # Add random private noise to both local messages but preserve Alice's
    # zero seed leak when her secret is uniformly averaged. Alice flips her
    # bit with probability 1/8. Bob maps his pair to an erasure symbol with
    # probability 1/4. Hence on positives TV=(3/4)^2=9/16; zeros unchanged.
    C=char(n)
    pri=1/(2*N)
    x_i=np.arange(N)
    seeds=np.arange(2*N)
    xphase=np.concatenate((C,-C),axis=1)
    A0=np.stack((.5+.375*xphase,.5-.375*xphase),axis=-1)
    A1=A0[:,:,::-1]
    assert np.all((A0+A1)/2==.5)
    for y in range(N):
        # Use the unique t=0 representative to label each unordered pair.
        bid=(seeds%N)^((seeds//N)*y)
        B=np.zeros((2*N,N+1))
        B[seeds,bid]=.75
        B[:,N]=.25
        T=np.einsum('xra,rb->xab',A0-A1,B)*pri
        true=(np.abs(T)*.5).sum(axis=(1,2))
        assert np.array_equal(true,(C[:,y]<0)*9/16)
        margB=pri*B.sum(axis=0)
        W=pri*B/margB[None,:]
        Z=np.einsum('xra,rb->xab',A0-A1,W)
        assert np.max(np.abs(Z))<=1
        app=(cheb_order(9,Z)*margB[None,None,:]*.5).sum(axis=(1,2))
        threshold=9/32
        assert np.array_equal(app>threshold,C[:,y]<0)
        assert np.min(np.abs(app-threshold))>1/8
    print("noisy one-bit transcript n=%d: TV 0 vs 9/16, zero Alice seed leakage, kernel sign margin PASS" % n)

if __name__=='__main__':
    check_shapes()
    check_hadamard()
    for n in range(1,7): check_noisy_construction(n)
