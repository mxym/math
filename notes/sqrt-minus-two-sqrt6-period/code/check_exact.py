#!/usr/bin/env python3
"""Independent exact-integer verifier for a sharp norm-six step sieve.

Verifies literal 682 nonzero-voltage negative paths, a complete finite
204800-point positive partition, and six-prime-factor algebra. Does not
import, invoke or trust the separate C++ witness producers.
"""
from collections import deque
from math import gcd,isqrt
from pathlib import Path
import gzip
import json

HERE=Path(__file__).resolve().parent
Q=1122
STEPS=((-2,-1),(-2,0),(-2,1),(-1,-1),(-1,0),(-1,1),
       (0,-1),(0,1),(1,-1),(1,0),(1,1),
       (2,-1),(2,0),(2,1))
GEN=((0,1),(1,1),(1,-1),(3,1),(3,-1),(3,2),(3,-2))


def require(c,msg):
    if not c:raise ValueError(msg)


def norm(p):
    a,b=p
    return a*a+2*b*b


def squarefree(n):
    return all(n%(k*k)!=0 for k in range(2,isqrt(n)+1))


def divides(g,z):
    a,b=g;c,d=z
    n=norm(g)
    return (a*c+2*b*d)%n==0 and (a*d-b*c)%n==0


def load(name):
    with gzip.open(HERE/name,'rt',encoding='utf-8') as f:
        return json.load(f)


def check_all_negative(data):
    require(type(data) is list and len(data)==682,
            'wrong number of lower-period certificates')
    observed=set()
    maxlength=0
    for case in data:
        q=case['q']
        require(type(q) is int and 1<=q<Q and squarefree(q) and q not in observed,
                'invalid or repeated squarefree scalar period')
        observed.add(q)
        start=tuple(case['start'])
        require(len(start)==2 and all(type(x) is int and 0<=x<q for x in start),
                'noncanonical period start')
        require(gcd(norm(start),q)==1,'path begins at forbidden lattice point')
        seq=case['steps']
        require(type(seq) is list and 0<len(seq)<=2000,
                'invalid negative step list')
        p=start
        for j in seq:
            require(type(j) is int and 0<=j<len(STEPS),'bad step index')
            da,db=STEPS[j]
            p=p[0]+da,p[1]+db
            require(gcd(norm(p),q)==1,
                    f'forbidden intermediate lattice point at q={q}')
        require(p!=start and all((p[k]-start[k])%q==0 for k in (0,1)),
                f'missing nonzero q-voltage in q={q}')
        maxlength=max(maxlength,len(seq))
    expected={q for q in range(1,Q) if squarefree(q)}
    require(observed==expected,'nonexhaustive squarefree lower period coverage')
    require(maxlength==561,'unexpected longest negative certificate')
    print('NEGATIVE: 682 explicit admissible nonzero-voltage walks for every squarefree q<1122; longest 561 steps')


def neighbors(p):
    a,b=p
    return ((a+da,b+db) for da,db in STEPS)


def check_positive(data):
    require(isinstance(data,dict) and set(data)=={'q','components'},
            'incorrect positive structure')
    require(data['q']==Q,'positive certificate scalar period differs')
    groups=data['components']
    require(type(groups) is list and len(groups)==6688,
            'wrong number of positive quotient components')
    owned=set()
    total=0
    maxsize=0
    for i,group in enumerate(groups):
        C={tuple(p) for p in group}
        require(C and len(C)==len(group),'empty or repeated finite group')
        if len(C)>maxsize:maxsize=len(C)
        total+=len(C)
        for p in C:
            require(len(p)==2 and all(type(k) is int for k in p),
                    'noninteger positive point')
            require(gcd(norm(p),Q)==1,'positive component contains forbidden point')
            r=p[0]%Q,p[1]%Q
            require(r not in owned,'repeated quotient residue')
            owned.add(r)
            for n in neighbors(p):
                require(gcd(norm(n),Q)!=1 or n in C,
                        f'component {i}: escaping allowed lattice edge')
        unseen=set(C)
        root=unseen.pop()
        todo=deque([root])
        while todo:
            for n in neighbors(todo.popleft()):
                if n in unseen:
                    unseen.remove(n)
                    todo.append(n)
        require(not unseen,f'component {i} disconnected')
    require((total,len(owned),maxsize)==(204800,204800,2283),
            'claimed complete quotient counts or maximum incorrect')
    num_allowed=0
    for a in range(Q):
        for b in range(Q):
            should_include=gcd(a*a+2*b*b,Q)==1
            if should_include:num_allowed+=1
            require(((a,b) in owned)==should_include,
                    'quotient residue missing or incorrectly included')
    require(num_allowed==204800,'allowed residue count mismatch')
    print('POSITIVE: all 1258884 residues checked; 204800 allowed; 6688 exact closed connected components; maximum 2283')



def exact_irreducible(z):
    """Exhaust all possible nonunit factors of norm <= sqrt(N(z))."""
    n=norm(z)
    if n<2:return False
    upper=isqrt(n)
    radius=isqrt(upper)
    for a in range(-radius,radius+1):
        for b in range(-radius,radius+1):
            k=a*a+2*b*b
            if 2<=k<=upper and divides((a,b),z):
                return False
    return True


def check_exceptional_closure(data):
    require(type(data) is list and len(data)==92,'wrong closure size')
    C={tuple(p) for p in data}
    require(len(C)==len(data),'duplicate exceptional closure points')
    E={(sign*a,sign*b) for a,b in GEN for sign in (-1,1)}
    require(len(E)==14 and E<=C,'incorrect exceptional prime generators')
    for p in C:
        require(len(p)==2 and all(type(x) is int for x in p),
                'noninteger exceptional point')
        require(p in E or gcd(norm(p),Q)==1,
                'forbidden non-exceptional closure vertex')
        for v in neighbors(p):
            require(v in C or (v not in E and gcd(norm(v),Q)!=1),
                    'exceptional closure has an escaping allowed neighbor')
    seen=set(E)
    queue=deque(E)
    while queue:
        for v in neighbors(queue.popleft()):
            if v in C and v not in seen:
                seen.add(v)
                queue.append(v)
    require(seen==C,'extraneous unreachable closure vertex')
    P={p for p in C if exact_irreducible(p)}
    require(len(P)==90 and C-P=={(-1,0),(1,0)},
            'incorrect finite exact prime factorization')
    require(E<=P,'exceptional generators not prime')
    unseen=set(P)
    root=unseen.pop()
    queue=deque([root])
    while queue:
        for v in neighbors(queue.popleft()):
            if v in unseen:
                unseen.remove(v)
                queue.append(v)
    require(not unseen,'irreducible exceptional closure disconnected')
    print('EXCEPTIONAL: 14 special primes, 92-point closed overgraph, 90 connected irreducible elements, exactly two units')


def check_prime_ideal_equivalence():
    require([norm(g) for g in GEN]==[2,3,3,11,11,17,17],
            'incorrect seven rational-prime norms')
    for a in range(Q):
        for b in range(Q):
            coprime=gcd(a*a+2*b*b,Q)==1
            allowed=not any(divides(g,(a,b)) for g in GEN)
            require(allowed==coprime,
                    'maximal principal ideals do not match the norm sieve')
    print('IDEALS: seven explicit prime-ideal congruence conditions exactly match the norm gcd predicate on all residues')


def check(negative,positive,exceptional):
    check_all_negative(negative)
    check_positive(positive)
    check_exceptional_closure(exceptional)
    check_prime_ideal_equivalence()
    print('ALL EXACT CERTIFICATES VERIFIED')


if __name__=='__main__':
    check(load('lower_cycles.json.gz'),load('positive_q1122.json.gz'),
          json.loads((HERE/'exceptional_closure.json').read_text()))
