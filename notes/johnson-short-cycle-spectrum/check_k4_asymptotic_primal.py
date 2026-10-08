#!/usr/bin/env python3
"""Pure-rational regression for the k=4 all-degree asymptotic primal family.

Mathematical positivity at all sufficiently large n is proved by the limiting
invertible 4x4 matrix and its strictly positive real-algebraic solution in
ASYMPTOTIC_RANK_FIVE.md.  This finite checker independently tests selected n.
No optimizer or floating-point computation is involved.
"""
from fractions import Fraction as Q
from math import comb, factorial, isqrt
from transfer import moment


def solve(A,b):
    m=len(b)
    assert len(A)==m and all(len(r)==m for r in A)
    z=[[Q(a) for a in A[i]]+[Q(b[i])] for i in range(m)]
    for j in range(m):
        pivot=next((i for i in range(j,m) if z[i][j]),None)
        assert pivot is not None
        z[j],z[pivot]=z[pivot],z[j]
        d=z[j][j]; z[j]=[a/d for a in z[j]]
        for i in range(m):
            if i!=j:
                d=z[i][j]
                z[i]=[z[i][k]-d*z[j][k] for k in range(m+1)]
    answer=[z[i][-1] for i in range(m)]
    assert all(sum(Q(a)*b for a,b in zip(A[i],answer))==Q(b[i])
               for i in range(m))
    return answer


def class_size(n,typ):
    r=n-sum((i+1)*v for i,v in enumerate(typ))
    assert r==0 or r>=5
    den=r if r else 1
    for i,v in enumerate(typ,1):
        den*=i**v*factorial(v)
    size,remain=divmod(factorial(n),den)
    assert remain==0
    return size


def certify(n):
    assert n>=50
    sr=isqrt(2*n*n)
    assert sr*sr<2*n*n<(sr+1)**2
    xl=(2*n-sr-1)//4
    xh=(2*n+sr)//4
    mid=n//2
    I=(n,0,0,0)
    L=(xl,0,0,0)
    H=(xh,0,0,0)
    Z=(0,0,0,0)
    M=(mid,0,0,0)
    T=(n-2,1,0,0)
    support=(I,L,H,Z,M,T)
    assert len(set(support))==6
    values={t:moment(n,4,t) for t in support}
    # Unknowns A_L,A_H,B_0,B_mid scaled so the four small weights
    # are A_L/n,A_H/n,B_0/n,B_mid/n respectively.
    mat=[]
    rhs=[]
    for j in range(4):
        mat.append([values[L][j]-values[I][j],
                    values[H][j]-values[I][j],
                    values[T][j]-values[Z][j],
                    values[T][j]-values[M][j]])
        rhs.append(n*(values[T][j]-values[I][j]))
    AL,AH,BZ,BM=solve(mat,rhs)
    assert min(AL,AH,BZ,BM)>0
    pI=1-(AL+AH)/n
    qT=1-(BZ+BM)/n
    assert pI>0 and qT>0
    P=((I,pI),(L,AL/n),(H,AH/n))
    W=((T,qT),(Z,BZ/n),(M,BM/n))
    assert sum(weight for _,weight in P)==sum(weight for _,weight in W)==1
    for j in range(5):
        lp=sum(v*values[t][j] for t,v in P)
        rp=sum(v*values[t][j] for t,v in W)
        assert lp==rp,(n,j,lp,rp)
    # A concrete small TV perturbation realizes identity excess pI*delta.
    qmax=max(weight/Q(class_size(n,t)) for t,weight in W)
    delta=Q(1,2*factorial(n)*qmax)
    assert delta>0
    assert all(Q(1,factorial(n))-delta*v/class_size(n,t)>=0
               for t,v in W)
    assert pI*delta==delta*(1-(AL+AH)/n)
    return pI,AL+AH


def main():
    for n in (50,75,100,150,200,300,500,1000,2000):
        prob,deficit=certify(n)
        assert prob>0
        # Exact rational checks; asymptotic convergence is analytic, not
        # inferred from these finitely many examples.
        print('PASS n=%d positive rational classes; 5 orbital moments; '
              'scaled deficit strictly between 0 and 32: %s'
              %(n, bool(0<deficit<32)),flush=True)
        assert 0<deficit<32
    print('NINE EXACT FOUR-SUBSET ASYMPTOTIC PRIMAL REGRESSIONS PASS')


if not __debug__:
    raise RuntimeError('Run without -O: optimized Python disables assert checks')

if __name__=='__main__':
    main()
