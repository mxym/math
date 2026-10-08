#!/usr/bin/env python3
"""Independent integer-only checker for radius-two R=Z[sqrt(-2)] results.

Does not import the producer; all conclusions have written lifting lemmas.
Explicit exceptions remain active with -O; optional enumeration cross-check.
"""
from collections import deque
from itertools import product
from math import gcd,isqrt
from pathlib import Path
import json

HERE=Path(__file__).resolve().parent
F=((-2,0),(-1,-1),(-1,0),(-1,1),(0,-1),(0,1),
   (1,-1),(1,0),(1,1),(2,0))
Q=6
T=(0,1); U=(1,1); V=(1,-1)
GEN=(T,U,V)
ALL=tuple(e for e in product(range(3),range(2),range(2)) if any(e))
REQUIRED=((1,0,0),(0,1,0),(0,0,1))


def require(cond,msg):
    if not cond:raise ValueError(msg)


def norm(p):
    a,b=p;return a*a+2*b*b


def multiply(p,q):
    a,b=p;c,d=q;return a*c-2*b*d,a*d+b*c


def divides(g,z):
    a,b=g;c,d=z;n=norm(g)
    return n>0 and (a*c+2*b*d)%n==0 and (a*d-b*c)%n==0


def generator(exponents):
    p=(1,0)
    for g,e in zip(GEN,exponents):
        for i in range(e):p=multiply(p,g)
    return p


def available(p,gens):
    return not any(divides(generator(e),p) for e in gens)


def norm_coprime(p):return gcd(norm(p),6)==1


def neighbors(p):
    return tuple((p[0]+dx,p[1]+dy) for dx,dy in F)


def connected(points):
    remaining=set(points)
    if not remaining:return False
    start=remaining.pop();queue=deque([start])
    while queue:
        for w in neighbors(queue.popleft()):
            if w in remaining:remaining.remove(w);queue.append(w)
    return not remaining


def exact_irreducible(p):
    n=norm(p)
    if n<2:return False
    bound=isqrt(n)
    amax=isqrt(bound)
    for a in range(-amax,amax+1):
        for b in range(-amax,amax+1):
            m=a*a+2*b*b
            if 2<=m<=bound and divides((a,b),p):return False
    return True


def prime_exceptions():
    return {tuple(sign*k for k in g) for g in GEN for sign in (-1,1)}


def check_partition(groups):
    require(len(groups)==4,'unexpected number of quotient components')
    owned=set()
    for part in groups:
        points={tuple(z) for z in part}
        require(len(points)==len(part)==2,'invalid component size/duplicate')
        require(connected(points),'positive component disconnected')
        for z in points:
            require(all(type(c) is int for c in z),'noninteger positive point')
            require(norm_coprime(z),'forbidden positive point')
            r=tuple(c%Q for c in z)
            require(r not in owned,'duplicate positive residue')
            owned.add(r)
            for w in neighbors(z):
                require(not norm_coprime(w) or w in points,
                        'escaping positive neighbor')
    for a in range(Q):
        for b in range(Q):
            require(((a,b) in owned)==norm_coprime((a,b)),
                    'missing or forbidden positive quotient residue')
    require(len(owned)==8,'incorrect number of allowed quotient residues')
    print('POSITIVE: 8 residues, 4 complete two-vertex components')


def check_exceptional_closure(points):
    closure={tuple(z) for z in points}
    require(len(closure)==len(points)==16,'closure count or duplicate wrong')
    exceptions=prime_exceptions()
    require(len(exceptions)==6 and exceptions<=closure,
            'six exceptional primes missing')
    for z in closure:
        require(z in exceptions or norm_coprime(z),
                'non-exception forbidden from overgraph')
        for w in neighbors(z):
            require((w in closure) or
                    (w not in exceptions and not norm_coprime(w)),
                    'unclosed exceptional overgraph')
    seen=set(exceptions);queue=deque(exceptions)
    while queue:
        for w in neighbors(queue.popleft()):
            if w in closure and w not in seen:
                seen.add(w);queue.append(w)
    require(seen==closure,'closure has extraneous unreachable points')
    primes={z for z in closure if exact_irreducible(z)}
    require(len(primes)==14 and (closure-primes)=={(-1,0),(1,0)},
            'finite primality classification differs')
    require(exceptions<=primes,'exceptional factors are not primes')
    remain=set(primes);cs=[]
    while remain:
        root=remain.pop();comp={root};queue=deque([root])
        while queue:
            for w in neighbors(queue.popleft()):
                if w in remain:
                    remain.remove(w);comp.add(w);queue.append(w)
        cs.append(comp)
    require(sorted(map(len,cs))==[7,7],'prime component sizes differ')
    expected=set(((0,1),(-1,1),(1,1),(-3,1),(-3,2),(3,1),(3,2)))
    require(expected in cs and {(a,-b) for a,b in expected} in cs,
            'seven-element exact prime components not reproduced')
    print('EXCEPTIONAL: finite closed 16 points; 14 primes in two 7-vertex components')


def check_cycle(item,period,good,label):
    start=tuple(item['start'])
    require(len(start)==2 and all(type(v) is int and 0<=v<period for v in start),
            label+': start is not a canonical residue')
    require(good(start),label+': starting vertex deleted')
    here=start
    steps=item['steps']
    require(type(steps) is list and 0<len(steps)<2000,label+': bad path length')
    for j in steps:
        require(type(j) is int and 0<=j<len(F),label+': bad step index')
        dx,dy=F[j]
        here=here[0]+dx,here[1]+dy
        require(good(here),label+': forbidden intermediate lattice point')
    require(here!=start and (here[0]-start[0])%period==0
            and (here[1]-start[1])%period==0,
            label+': not a nonzero period walk')
    return len(steps)


def check_negative(cases):
    require(len(cases)==3,'wrong number of missing-ideal witnesses')
    seen=set()
    lens=[]
    for item in cases:
        omitted=tuple(item['missing'])
        require(omitted in REQUIRED and omitted not in seen,'incorrect or duplicate omitted ideal')
        seen.add(omitted)
        remaining=[e for e in ALL if e!=omitted]
        lens.append(check_cycle(item,Q,lambda p:available(p,remaining),
                                'omitted '+str(omitted)))
    require(seen==set(REQUIRED),'incomplete maximal-failure coverage')
    print('MAXIMAL FAILURES: three verified 6-period nonzero-voltage walks',lens)


def check_lower(cases):
    periods={}
    for item in cases:
        p=item['q']
        require(type(p) is int and 1<=p<6 and p not in periods,
                'bad lower period index')
        periods[p]=check_cycle(item,p,lambda z:gcd(norm(z),p)==1,
                               'lower period '+str(p))
    require(set(periods)==set(range(1,6)),'incomplete lower period coverage')
    print('LOWER: nonzero-voltage walks for all periods 1..5',sorted(periods.items()))


def check_sieve(gens):
    allowed_set={(a,b) for a in range(Q) for b in range(Q) if available((a,b),gens)}
    seen=set()
    for root in allowed_set:
        if root in seen:continue
        lift={root:root};queue=deque([root]);seen.add(root)
        while queue:
            res=queue.popleft();p=lift[res]
            for w in neighbors(p):
                r=w[0]%Q,w[1]%Q
                if r not in allowed_set:continue
                if r in lift:
                    if lift[r]!=w:return False
                else:
                    seen.add(r);lift[r]=w;queue.append(r)
    return True


def check_all_ideal_subsets():
    count=0
    for mask in range(1<<len(ALL)):
        gens=[ALL[j] for j in range(len(ALL)) if mask&(1<<j)]
        predicted=all(e in gens for e in REQUIRED)
        actual=check_sieve(gens)
        require(predicted==actual,'incorrect full sieve classification at '+str(mask))
        count+=actual
    require(count==256,'wrong number of successful divisor subfamilies')
    print('EXHAUSTIVE: all 2048 ideal subsets tested, 256 successful exactly as predicted')


def check(data,exhaustive=True):
    require(set(data)=={'positive_components','exceptional_closure',
                        'maximal_failure_cycles','lower_period_cycles'},
            'incorrect certificate keys')
    require(len(ALL)==11 and len(set(generator(e) for e in ALL))==11,
            'prime factor divisor list incorrect')
    require(all(divides(generator(e),(6,0)) for e in ALL),'invalid divisor of scalar six')
    check_partition(data['positive_components'])
    check_exceptional_closure(data['exceptional_closure'])
    check_negative(data['maximal_failure_cycles'])
    check_lower(data['lower_period_cycles'])
    if exhaustive:check_all_ideal_subsets()
    print('ALL EXACT CERTIFICATES VERIFIED')


if __name__=='__main__':
    check(json.loads((HERE/'certificate.json').read_text()))
