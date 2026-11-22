#!/usr/bin/env python3
"""Exact checks of the local lcm Euler factors, zero offset, and simplex-gap rates.
Uses rationals; not a numerical estimate of true prime distribution.
"""
from fractions import Fraction as F
from itertools import combinations, product
from math import comb, factorial, prod

def need(flag, message):
    if not flag:
        raise RuntimeError(str(message))

def powerset(S):
    S = tuple(S)
    return [frozenset(T) for r in range(len(S)+1) for T in combinations(S, r)]

def check_lcm():
    P = (2, 3, 5, 7, 13)
    count = 0
    for extra in powerset(P[1:]):
        Nf = extra | {2}
        avail = set(P) - Nf
        atom = {p:F(1) - F(1,p*(p-1)) for p in avail}
        for d in powerset(avail):
            lcm_sum = F(0)
            for e in powerset(avail):
                # The actual prime modulus is [d,e²], not d e².
                phi = prod((p-1)*(p if p in e else 1) for p in d | e)
                lcm_sum += F((-1)**len(e), phi)
            euler = prod(atom[p] if p not in d else F(1,p) for p in avail)
            inverse = prod(atom.values()) * prod(F(1,p)/atom[p] for p in d)
            need(lcm_sum == euler == inverse, (Nf,d,lcm_sum,euler,inverse))
            count += 1
    return count

def g(u, lo, hi, degree):
    if u <= lo:
        return F(1)
    if u >= hi:
        return F(0)
    t = (u-lo)/(hi-lo)
    poly = sum(F((-1)**j*comb(degree,j),degree+j+1)*t**(degree+j+1)
               for j in range(degree+1))
    return 1 - poly*F(factorial(2*degree+1),factorial(degree)**2)

def check_score():
    # Positive exact rational proxies for individual prime logs, normalized
    # to sum 1. The identities are formal in these arguments.
    count = 0
    settings = [(F(1,11),F(1,5),F(2,5)),
                (F(1,13),F(2,7),F(3,7)),
                (F(1,3),F(3,7),F(13,28))]
    for r in range(1,7):
        S = frozenset(range(r))
        parts = powerset(S)
        tr = []
        for t in product(range(3),repeat=r):
            v = [frozenset(i for i,j in enumerate(t) if j==k) for k in range(3)]
            tr.append(v)
        for source in combinations(range(1,9),r):
            u = [F(t,sum(source)) for t in source]
            logs = {s:sum((u[i] for i in s),F(0)) for s in parts}
            ell = F(r==1)
            for lo,hi,cap in settings:
                ev = {s:g(logs[s],lo,hi,3) for s in parts}
                s_g = sum(((-1)**len(s)*ev[s] for s in parts),F(0))
                direct = sum(((-1)**len(s)*(1-ev[s])*logs[S-s]
                              for s in parts),F(0))
                direct += sum(((-2)**len(c)*logs[s]*ev[c|s] for c,a,s in tr
                               if all(u[i]<cap for i in c)),F(0))
                need(direct == ell - s_g, (r,source,lo,hi,cap,direct,ell-s_g))
                if r==1:
                    need(direct == 0, ("prime row",lo,hi,cap))
                partial = [ev[s] for s in parts]
                # Applying all differences to independently represented function values.
                vals = {s:w for s,w in zip(parts,partial)}
                for i in range(r):
                    vals = {s:vals[s|{i}]-vals[s] for s in vals if i not in s}
                need(vals[frozenset()]*(-1)**r == s_g,(r,source,"difference signs"))
                count += 1
    return count

def check_gap_rates():
    count=0
    for n in range(1,65):
        for d in range(1,n+1):
            for mark in (F(0),F(1,2)):
                # v_j=sum_{i>=j} w_i. The coefficient of each w_i
                # is obtained independently by counting included v_j.
                rates=[sum((F(1) for j in range(d) if i>=j),F(0))-mark
                       for i in range(n)]
                expected=[F(min(i+1,d))-mark for i in range(n)]
                need(rates == expected and min(rates)>0,(n,d,mark))
                integral=prod(F(1,r) for r in rates)
                if mark==0:
                    need(integral == F(1,factorial(d)*d**(n-d)),(n,d))
                else:
                    need(integral == prod(F(2,2*j-1) for j in range(1,d+1))
                                      *F(2,2*d-1)**(n-d),(n,d))
                count += 1
    return count

def main():
    out=check_lcm(),check_score(),check_gap_rates()
    print("PASS local factors, exact completed scores/differences, ordered gap rates:",*out)

if __name__=="__main__":
    main()
