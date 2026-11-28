#!/usr/bin/env python3
"""Exact symbolic finite checks for bounded quantum messages on classical batches.

Requires SymPy. Tests rational/complex matrix identities, not an inference rule.
"""
from itertools import product
from sympy import I, Matrix, Rational as R, diag, eye, kronecker_product, zeros


def pt_first(X,a,b):
    return Matrix(b,b,lambda i,j:sum(X[k*b+i,k*b+j] for k in range(a)))


def pt_second(X,a,b):
    return Matrix(a,a,lambda i,j:sum(X[i*b+k,j*b+k] for k in range(b)))


def proj(v):
    return v*v.H


def pos(A):
    # Hermitian exact arithmetic. The examples are dimension at most 8.
    assert A==A.H
    assert A.is_positive_semidefinite is True, A


def construct_ensemble():
    V=[eye(2),Matrix([[0,1],[1,0]]),diag(1,-1),diag(1,I)]
    refs=((R(3,5),R(4,5)),(R(5,13),R(12,13)),(R(8,17),R(15,17)))
    tests=[0,0,0]
    for u,v in refs:
        omega=diag(u*u,v*v)
        planted=proj(Matrix([u,0,0,v]))
        tau=kronecker_product(eye(4)/4,omega)
        gamma=8
        blocks=[]
        for idx,U in enumerate(V):
            Q=kronecker_product(U,eye(2))
            bell=Q*planted*Q.H
            if idx%2==0:
                sigma=diag(bell,zeros(4))
            else:
                sigma=diag(bell/3,2*bell/3)
            assert pt_first(sigma,4,2)==omega
            pos(gamma*tau-sigma)
            assert (sigma*tau.inv()*sigma).trace()<=gamma
            blocks.append(sigma)
            tests[0]+=1
        fams=((R(1,2),R(0),R(1,5),R(3,10)),(R(0),R(2,3),R(1,6),R(1,6)),
              (R(1,4),R(1,4),R(1,4),R(1,4)),(R(1,3),R(1,6),R(1,6),R(1,3)))
        for p,q,nu in product(fams,fams,fams[-2:]):
            lam=sum((a-b)**2/(4*c) for a,b,c in zip(p,q,nu))
            D=sum(((a-b)*P/2 for a,b,P in zip(p,q,blocks)),zeros(8))
            assert (D*tau.inv()*D).trace()<=lam*gamma
            tests[1]+=1
        # For a single maximally entangled report, the factor D^2 is attained.
        if u==refs[0][0]:
            E=Matrix([1,0,0,1])
            Bell=proj(E)/2
            assert (Bell*(4*eye(4))*Bell).trace()==4
            tests[2]+=1
    return tuple(tests)


def purify():
    cases=0
    for u,v in ((R(3,5),R(4,5)),(R(5,13),R(12,13))):
        D=diag(u,v)
        omega=D*D
        X=proj(Matrix([u,0,0,v]))
        for z in (R(1,7),-R(1,7),I/7,-I/7):
            A=Matrix([[1,z],[z.conjugate(),1]])
            rho=D*A*D
            k=2
            pos(rho)
            pos(k*omega-rho)
            effect=(D.inv()*rho*D.inv()).T/k
            pos(effect)
            pos(eye(2)-effect)
            got=pt_second(kronecker_product(eye(2),effect)*X,2,2)
            assert got==rho/k
            for U in (eye(2), Matrix([[0,1],[1,0]]), diag(1,I)):
                Lift=kronecker_product(U,eye(2))
                transformed=Lift*X*Lift.H
                after=pt_second(kronecker_product(eye(2),effect)*transformed,2,2)
                assert after==U*rho*U.H/k
                cases+=1
    return cases


def singular_outside():
    # The unused last outside direction must not require inversion.
    v=Matrix([1,0,0,0,1,0])
    a=proj(v)/2
    assert pt_first(a,2,3)==diag(R(1,2),R(1,2),0)
    rho=kronecker_product(eye(2)/2,diag(R(1,2),R(1,2),0))
    pos(4*rho-a)
    inv=diag(4,4,0,4,4,0)
    assert (a*inv*a).trace()==4


if __name__=="__main__":
    print("PASS exact assisted state and weighted-variance checks:",construct_ensemble())
    print("PASS complex postselection and commute checks:",purify())
    singular_outside()
    print("PASS singular reference support")
