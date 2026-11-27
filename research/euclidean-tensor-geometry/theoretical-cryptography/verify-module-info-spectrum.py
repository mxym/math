#!/usr/bin/env python3
"""Exact finite checks for the module hashing spectrum inequalities."""
from collections import Counter
from fractions import Fraction as F
from itertools import product
from math import comb


class Module:
    def __init__(self, name, ring_size, add, action, subs):
        self.name, self.R, self.M = name, range(ring_size), range(4)
        self.add, self.action, self.subs = add, action, tuple(map(tuple,subs))
        self.minus = tuple(next(y for y in self.M if add(x,y)==0) for x in self.M)
        self.proj = {J:{x:min(add(x,v) for v in J) for x in self.M} for J in self.subs}

    def solve(self, A, cols, k):
        m = len(cols)
        y = []
        for i in range(k):
            val = 0
            for j,x in enumerate(cols):
                val = self.add(val,self.action(A[i*m+j],x))
            y.append(val)
        return tuple(y)

    def difference_module(self, x, y):
        S = {0}
        for a,b in zip(x,y):
            v = self.add(a,self.minus[b])
            S = {self.add(u,self.action(r,v)) for u in S for r in self.R}
        return tuple(sorted(S))


def matrix2_action(a,x):
    return (((a&3)&x).bit_count()%2)|((((a>>2)&x).bit_count()%2)<<1)


def powers(law,m):
    out = {}
    for x in product(range(4),repeat=m):
        p = F(1)
        for z in x:
            p *= law[z]
        if p:
            out[x] = p
    assert sum(out.values()) == 1
    return out


def qproj(P,projection):
    p = Counter()
    for x,v in P.items():
        p[tuple(projection[a] for a in x)] += v
    return p


def cut_flags(S, P, x, k, eps):
    good, bad = True, False
    for J in S.subs:
        q = len(S.M)//len(J)
        z = tuple(S.proj[J][a] for a in x)
        mass = P[J][z]
        good &= (mass <= eps/F(q**k))
        bad |= (mass > 1/(eps*q**k))
    return good,bad


def push(source, images):
    p = Counter()
    for x,v in source.items():
        p[images[x]] += v
    return p


def test(S,m,k,y_sources,eps_values):
    Cs = len(S.M)**k
    all_x = tuple(product(S.M,repeat=m))
    all_y = tuple(product(S.M,repeat=k))
    matrices = tuple(product(S.R,repeat=m*k))
    output = [dict((x,S.solve(A,x,k)) for x in all_x) for A in matrices]
    all_im = {}
    for v in all_x:
        J = S.difference_module(v,(0,)*m)
        c = sum(p[v]==(0,)*k for p in output)
        assert F(c,len(output)) == F(1,len(J)**k)
        all_im[v] = J
    D = []
    for y_weight,law in y_sources:
        P = powers(law,m)
        D.append([sum(abs(push(P,out).get(z,0)-F(1,Cs)) for z in all_y)/2 for out in output])
    joint = [sum(yw*Ds[j] for (yw,_),Ds in zip(y_sources,D)) for j in range(len(output))]
    average = sum(joint)/len(joint)
    ntests = useful = 0
    for eps in eps_values:
        blo,bhi = F(0),F(0)
        for yw,law in y_sources:
            P = powers(law,m)
            quot = {J:qproj(P,S.proj[J]) for J in S.subs}
            flags = {x:cut_flags(S,quot,x,k,eps) for x in P}
            Q = {x:P[x] for x in P if flags[x][0]}
            g = sum(Q.values(),F(0))
            blo += yw*sum(P[x] for x in P if flags[x][1])
            bhi += yw*(1-g)
            for J in S.subs:
                assert sum(p*p for p in qproj(Q,S.proj[J]).values()) <= g*eps/(len(S.M)//len(J))**k
            acc = F(0)
            for out in output:
                dist = push(Q,out)
                acc += sum((dist.get(u,0)-g/Cs)**2 for u in all_y)
            lhs = Cs*acc/len(output)
            rhs = F(0)
            for x,y in product(Q,repeat=2):
                v = tuple(S.add(a,S.minus[b]) for a,b in zip(x,y))
                rhs += Q[x]*Q[y]*((len(S.M)//len(all_im[v]))**k-1)
            assert lhs == rhs <= len(S.subs)*g*eps
        assert min(joint) >= blo-len(S.subs)*eps
        useful += blo-len(S.subs)*eps > 0
        if average>bhi:
            assert 4*(average-bhi)**2 <= len(S.subs)*eps
        ntests += 1
    print(f"PASS {S.name}, m={m}, k={k}: {len(matrices)} matrices, "
          f"{len(all_x)} exact collision types, {ntests} one-shot bounds ({useful} positive converse)")


def binomial_counts(n):
    # p=1/4, numerator under common denominator 4^n.
    return [comb(n,j)*3**(n-j) for j in range(n+1)]


def check_correlated_example():
    for n in (64,256,1024,4096):
        counts = binomial_counts(n)
        pref = [0]
        for z in counts:
            pref.append(pref[-1]+z)
        den = pref[-1]
        assert den == 4**n
        bound = n//4
        core = pref[bound]
        # x < n/4 OR x+y < n/2, using two independent copies.
        joint = (core*den+sum(counts[j]*pref[max(0,n//2-j)] for j in range(bound,n+1)))
        uncorrelated = 1-F(den-core,den)**2
        correlated = F(joint,den**2)
        assert 0<correlated<uncorrelated<1
        if n>=1024:
            assert abs(correlated-F(5,8))<F(3,100)
            assert abs(uncorrelated-F(3,4))<F(3,100)
        print(f"PASS centered input union at n={n}: correlated={float(correlated):.7g}, "
              f"product={float(uncorrelated):.7g}")


if __name__=="__main__":
    z4 = Module("Z/4",4,lambda a,b:(a+b)%4,lambda a,x:a*x%4,[(0,),(0,2)])
    z8 = Module("Z/8 on Z/4",8,lambda a,b:(a+b)%4,lambda a,x:a*x%4,[(0,),(0,2)])
    prod2 = Module("F2 x F2",4,lambda a,b:a^b,lambda a,x:a&x,[(0,),(0,1),(0,2)])
    mat = Module("M2(F2) on F2^2",16,lambda a,b:a^b,matrix2_action,[(0,)])
    unif = ((F(1),[F(1,4)]*4),)
    conditional = ((F(1,3),[F(1,4)]*4),
                   (F(2,3),[F(1,2),F(1,8),F(1,4),F(1,8)]))
    point = ((F(1),[F(1),F(0),F(0),F(0)]),)
    eps_values = (F(1,2),F(1,3),F(1,4),F(1,8))
    for S in (z4,z8,prod2,mat):
        test(S,2,1,unif,eps_values)
        test(S,2,1,conditional,eps_values)
    test(prod2,2,2,point,eps_values)
    check_correlated_example()
