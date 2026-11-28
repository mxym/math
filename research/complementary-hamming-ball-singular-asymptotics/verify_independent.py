#!/usr/bin/env python3
"""Independent recurrence, explicit one-qubit tilt and scaled norm brackets."""
from math import acosh, comb, cosh, exp, hypot, log, log1p, pi, sqrt


def entropy(x):
    return -x*log(x)-(1-x)*log1p(-x)


def formulas(p,q):
    delta = sqrt((1-2*p)**2-4*q*(1-q))
    z = 2*q/(1-2*p+delta)
    A = .5*log((1-p)/p) + log1p(-z)-log1p(z)
    B = .5*log(q/(1-q))-log(z)
    D = .5*acosh(cosh(A)*cosh(B))
    R = -.5*log(2)+.5*(entropy(p)-entropy(q))+p*log1p(-z)+(1-p)*log1p(z)-q*log(z)
    sigma2 = z*delta/(1-z*z)
    chi = (q*(1-q)/(p*(1-p)))**.25
    assert A>0 and B>0 and D>0 and R<0
    assert abs(R-D+((1-2*p)*A+(1-2*q)*B)/2)<3e-15
    return A,B,D,R,sigma2,chi


def row(m,x,cap):
    ans = [1]
    if cap:
        ans.append(m-2*x)
    for j in range(1,cap):
        numerator = (m-2*x)*ans[j]-(m-j+1)*ans[j-1]
        quotient,remainder = divmod(numerator,j+1)
        assert not remainder
        ans.append(quotient)
    return ans


def block(n,a,b,r,corner,tilt):
    m = n-2*r
    A,B,D,R = tilt
    cv = [log(comb(m,j)) for j in range(max(a,b)-r+1)]
    ret = []
    for i,x in enumerate(range(a-r,-1,-1)):
        source = row(m,x,b-r)
        scaled = []
        for j,y in enumerate(range(b-r,-1,-1)):
            k = source[y]
            if not k:
                scaled.append(0.)
                continue
            val = log(abs(k))+.5*(cv[x]-cv[y]-m*log(2))
            assert val <= n*R-2*r*D-i*A-j*B+1e-10
            scaled.append((1 if k>0 else -1)*exp(val-corner))
        ret.append(scaled)
    return ret


def brackets(M):
    # Lower bound from a unit test vector; Frobenius is a rigorous upper
    # bound in exact arithmetic. The numerical comparison has slack.
    cols = list(zip(*M))
    d = len(cols)
    v = [1/sqrt(d)]*d
    for i in range(8):
        u = [sum(x*y for x,y in zip(v,row)) for row in M]
        w = [sum(x*y for x,y in zip(u,col)) for col in cols]
        size = hypot(*w)
        assert size > 0
        v = [x/size for x in w]
    return (hypot(*(sum(x*y for x,y in zip(v,row)) for row in M)),
            hypot(*(x for row in M for x in row)))


algebra = 0
for a in range(1,101):
    for b in range(1,101):
        p,q = a/200,b/200
        if (1-2*p)**2+(1-2*q)**2 <= 1+1e-12:
            continue
        A,B,D,R,_,_ = formulas(p,q)
        rb = formulas(q,p)
        assert max(abs(A-rb[1]), abs(B-rb[0]), abs(D-rb[2]), abs(R-rb[3])) < 2e-14
        algebra += 1
print(f"saddle/closed-form tilt dual and transpose identities: {algebra} points")

checks=0
for U,V in [(79,81),(41,176),(175,43)]:
    u,v=U/1000,V/1000
    A0,B0,D0,_,_,_ = formulas(u,v)
    for n in (160,400,2500):
        a,b=n*U//1000,n*V//1000
        A,B,D,R,sigma2,chi=formulas(a/n,b/n)
        corner=n*R+log(chi)-.5*log(2*pi*n*sigma2)
        constant=1/sqrt((1-exp(-2*A0))*(1-exp(-2*B0)))
        all_norms=[]
        for r in (0,1,2,4):
            M=block(n,a,b,r,corner,(A,B,D,R))
            lo,hi=brackets(M)
            expected=constant*exp(-2*r*D0)
            all_norms.append((lo,hi))
            if n==2500:
                assert .91*expected<lo<=hi<1.09*expected
                # Independent check of the local geometric rank-one kernel.
                for i,j in [(0,0),(0,1),(1,0),(1,2),(2,1)]:
                    p=exp(-2*r*D0-i*A0-j*B0)
                    assert abs(M[i][j]/p-1)<.18
            checks+=1
        assert all_norms[0][0]>all(x[1] for x in all_norms[1:])
        print(f"n={n:4} radii={u:.3f},{v:.3f}: root/pred in "
              f"[{all_norms[0][0]/constant:.5f},{all_norms[0][1]/constant:.5f}], "
              f"sector1/root in [{all_norms[1][0]/all_norms[0][1]:.5f},"
              f"{all_norms[1][1]/all_norms[0][0]:.5f}]")
print(f"recurrence scaled Frobenius/Rayleigh brackets: {checks} sector matrices")
