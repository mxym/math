#!/usr/bin/env python3
"""Independent exact-integer verifier for Z[sqrt(-2)] finite proof witnesses.

No float, solver, randomized search, or call to the discovery producer.
The paper proves how the checked finite predicates imply infinite claims.
"""
from collections import deque
from itertools import product
from math import gcd, isqrt
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent
STEP=((-1,-1),(-1,0),(-1,1),(0,-1),(0,1),(1,-1),(1,0),(1,1))
G0=(0,1)
G1=(1,1)
G2=(1,-1)
R=6
DIVISORS=tuple(z for z in product(range(3),range(2),range(2)) if any(z))
PAIR1=frozenset(((1,0,0),(0,1,0)))
PAIR2=frozenset(((1,0,0),(0,0,1)))
TRIPLE=frozenset(((2,0,0),(0,1,0),(0,0,1)))
POSITIVE=(PAIR1,PAIR2,TRIPLE)
OMIT=(frozenset(((1,0,0),(2,0,0))),
      frozenset(((1,0,0),(0,1,0))),
      frozenset(((1,0,0),(0,0,1))),
      frozenset(((0,1,0),(0,0,1))))


def require(ok,msg):
    if not ok:raise ValueError(msg)


def norm(z):
    return z[0]*z[0]+2*z[1]*z[1]


def mul(x,y):
    a,b=x;c,d=y
    return a*c-2*b*d,a*d+b*c


def divisor_of(g,z):
    a,b=g;c,d=z;n=norm(g)
    return n>0 and (a*c+2*b*d)%n==0 and (a*d-b*c)%n==0


def gen(e):
    p=(1,0)
    for g,ex in ((G0,e[0]),(G1,e[1]),(G2,e[2])):
        for _ in range(ex):p=mul(p,g)
    return p


def allowed(z,generators):
    return not any(divisor_of(gen(e),z) for e in generators)


def nbr(z):
    return tuple((z[0]+a,z[1]+b) for a,b in STEP)


def connected(group):
    unused=set(group)
    if not unused:return False
    root=unused.pop();todo=[root]
    while todo:
        for z in nbr(todo.pop()):
            if z in unused:unused.remove(z);todo.append(z)
    return not unused


def verify_partition(entry,basis,expected_sizes):
    generators=[tuple(e) for e in entry['generators']]
    require(set(generators)==set(basis) and len(generators)==len(basis),
            'wrong positive generator family')
    owned=set();sizes=[]
    for seq in entry['components']:
        C={tuple(p) for p in seq}
        require(C and len(C)==len(seq), 'duplicate or empty finite component')
        require(connected(C),'disconnected positive component')
        for point in C:
            require(len(point)==2 and all(type(t) is int for t in point),
                    'noninteger point')
            require(allowed(point,basis),'forbidden vertex included')
            residue=tuple(t%R for t in point)
            require(residue not in owned,'non-unique residue representative')
            owned.add(residue)
            for v in nbr(point):
                require(not allowed(v,basis) or v in C,
                        'positive component has escaping neighbor')
        sizes.append(len(C))
    for a in range(R):
        for b in range(R):
            require(((a,b) in owned)==allowed((a,b),basis),
                    'quotient coverage missing or forbidden residue included')
    require(sorted(sizes)==sorted(expected_sizes),'component sizes differ')
    return len(owned),sizes


def check_walk(base,steps,q,test,label):
    start=tuple(base)
    require(len(start)==2 and all(type(x) is int and 0<=x<q for x in start),
            label+': start not canonical')
    require(test(start),label+': forbidden initial point')
    require(steps and len(steps)<2000,label+': invalid step length')
    point=start
    for j in steps:
        require(type(j) is int and 0<=j<8,label+': invalid step')
        v=STEP[j]
        point=(point[0]+v[0],point[1]+v[1])
        require(test(point),label+': walk enters deleted ideal')
    require(point!=start and all((point[k]-start[k])%q==0 for k in (0,1)),
            label+': path lacks nonzero-period voltage')
    return len(steps)


def check_sieve(generators):
    """Independent full 36-state quotient BFS; no generator output consulted."""
    V={(a,b) for a in range(R) for b in range(R) if allowed((a,b),generators)}
    done=set()
    for start in sorted(V):
        if start in done:continue
        lift={start:start};todo=deque([start]);done.add(start)
        while todo:
            residue=todo.popleft()
            a,b=lift[residue]
            for da,db in STEP:
                w=(a+da,b+db)
                y=(w[0]%R,w[1]%R)
                if y not in V:continue
                if y in lift:
                    if lift[y]!=w:return False
                else:
                    lift[y]=w;todo.append(y);done.add(y)
    return True


def irreducible(z):
    n=norm(z)
    if n<2:return False
    lim=isqrt(n)
    for a in range(-isqrt(lim),isqrt(lim)+1):
        for b in range(-isqrt(lim),isqrt(lim)+1):
            m=a*a+2*b*b
            if 2<=m<=lim and divisor_of((a,b),z):return False
    return True


def check_math_structure():
    require(len(DIVISORS)==11,'unexpected divisor index')
    gset={gen(e) for e in DIVISORS}
    require(len(gset)==11,'duplicate divisor representative')
    require(all(divisor_of(gen(e),(6,0)) for e in DIVISORS),
            'a canonical divisor does not divide six')
    exceptional={x for g in (G0,G1,G2) for x in (g,(-g[0],-g[1]))}
    require(len(exceptional)==6 and all(irreducible(z) for z in exceptional),
            'exceptional prime family wrong')
    for z in exceptional:
        for w in nbr(z):
            require(not irreducible(w) or w in exceptional,
                    'exceptional prime has unaccounted prime neighbor')
    unused=set(exceptional);sizes=[]
    while unused:
        root=unused.pop();part={root};todo=[root]
        while todo:
            for w in nbr(todo.pop()):
                if w in unused:unused.remove(w);part.add(w);todo.append(w)
        sizes.append(len(part))
    require(sorted(sizes)==[3,3],'exceptional components wrong')
    require(irreducible((3,1)) and irreducible((3,2)),
            'required ordinary-prime matching example absent')
    return sizes


def check_certificate(data, exhaustive=True):
    require(set(data)=={'positive','maximal_failures','lower_periods'},
            'wrong certificate section keys')
    seen=set()
    counts=[]
    for entry in data['positive']:
        basis=frozenset(tuple(e) for e in entry['generators'])
        require(basis in POSITIVE and basis not in seen,'invalid positive basis')
        seen.add(basis)
        expected=[2]*6 if basis!=TRIPLE else [4,8]
        counts.append(verify_partition(entry,basis,expected))
    require(seen==set(POSITIVE),'missing positive basis')
    print('POSITIVE: 3 finite exact quotient decompositions:',counts)

    seen=set();lengths=[]
    for entry in data['maximal_failures']:
        excluded=frozenset(tuple(e) for e in entry['omitted'])
        require(excluded in OMIT and excluded not in seen,'invalid maximal failure mask')
        seen.add(excluded)
        gens=set(DIVISORS)-set(excluded)
        lengths.append(check_walk(entry['start'],entry['steps'],R,
                                  lambda z:not any(divisor_of(gen(e),z) for e in gens),
                                  f'maximal failure {sorted(excluded)}'))
    require(seen==set(OMIT),'missing maximal failure')
    print('NEGATIVE: 4 complete maximal failure voltage witnesses:',lengths)

    periods={}
    for entry in data['lower_periods']:
        q=entry['q']
        require(type(q) is int and 1<=q<6 and q not in periods,
                'duplicate/out-of-range lower period')
        periods[q]=check_walk(entry['start'],entry['steps'],q,
                              lambda z:gcd(norm(z),q)==1,
                              f'lower period {q}')
    require(set(periods)==set(range(1,6)),'lower period coverage incomplete')
    print('LOWER: all scalar periods 1..5 excluded:',sorted(periods.items()))

    sizes=check_math_structure()
    print('IRREDUCIBLES: exactly two exceptional 3-vertex components; sizes',sizes)
    if exhaustive:
        successful=0
        for mask in range(1<<len(DIVISORS)):
            gens=[DIVISORS[j] for j in range(len(DIVISORS)) if (mask>>j)&1]
            predicted=any(basis <= set(gens) for basis in POSITIVE)
            actual=check_sieve(gens)
            require(actual==predicted,'exhaustive independent classification mismatch '+str(mask))
            successful+=actual
        require(successful==896,'unexpected successful-sieve count')
        print('EXHAUSTIVE: all 2048 ideal subfamilies agree; successful:',successful)
    print('ALL EXACT CERTIFICATES VERIFIED')


if __name__=='__main__':
    data=json.loads((HERE/'certificate.json').read_text())
    check_certificate(data)
