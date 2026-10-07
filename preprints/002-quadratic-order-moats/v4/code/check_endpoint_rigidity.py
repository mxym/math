#!/usr/bin/env python3
from itertools import product,combinations
import json,math
from pathlib import Path

F8={(a,b) for a in (-1,0,1) for b in (-1,0,1) if (a,b)!=(0,0)}
PRIMES=((1,1),(2,1),(2,-1),(3,2),(3,-2))
Q=130

def require(c,m):
    if not c:raise ValueError(m)

def mul(x,y):
    a,b=x;c,d=y
    return (a*c-b*d,a*d+b*c)

def canon(z):
    a,b=z
    return min((a,b),(-b,a),(-a,-b),(b,-a))

def powg(z,n):
    r=(1,0)
    for _ in range(n):r=mul(r,z)
    return r

def independent_divisors():
    out=set()
    for es in product(range(3),range(2),range(2),range(2),range(2)):
        z=(1,0)
        for p,e in zip(PRIMES,es):
            z=mul(z,powg(p,e))
        out.add(canon(z))
    out.remove(canon((1,0)))
    require(len(out)==47,'divisor count')
    return sorted(out)

def scalar_period(g):
    a,b=g;D=a*a+b*b;return D//math.gcd(abs(a),abs(b))

def divisible(z,g):
    x,y=z;a,b=g;D=a*a+b*b
    return (a*x+b*y)%D==0 and (-b*x+a*y)%D==0

def allowed(z,gs):return all(not divisible(z,g) for g in gs)

def verify_walk(gs,w):
    root=tuple(w['root']);steps=[tuple(d) for d in w['steps']]
    require(all(d in F8 for d in steps),'bad step')
    require(allowed(root,gs),'bad root')
    z=root
    for d in steps:
        z=(z[0]+d[0],z[1]+d[1])
        require(allowed(z,gs),'forbidden visit')
    dx=z[0]-root[0];dy=z[1]-root[1]
    require(dx%Q==0 and dy%Q==0,'not Q-closed')
    v=(dx//Q,dy//Q)
    require(v!=(0,0),'zero voltage')
    require(list(v)==w['voltage'],'stored voltage')
    cnt=sum(allowed((x,y),gs) for x in range(Q) for y in range(Q))
    require(cnt==w['allowed_residues'],'allowed count')
    return len(steps)

def main():
    here=Path(__file__).resolve().parent
    d=json.loads((here/'endpoint_rigidity.json').read_text())
    require(d['schema']=='mxym-math-002-v4-gaussian-f8-endpoint-rigidity-1','schema')
    require(d['period']==Q,'period')
    require([tuple(x) for x in d['prime_generators']]==list(PRIMES),'prime list')
    divs=independent_divisors()
    require([tuple(x) for x in d['all_nonunit_divisor_ideals']]==divs,'incomplete divisor ideals')
    require(all(130%scalar_period(a)==0 for a in divs),'bad scalar period')

    expected_sub=[tuple(c) for k in range(5) for c in combinations(range(5),k)]
    cases=d['proper_prime_subset_failures']
    require([tuple(x['indices']) for x in cases]==expected_sub,'proper subset coverage')
    lengths=[]
    for x in cases:
        gs=tuple(tuple(g) for g in x['generators'])
        require(gs==tuple(PRIMES[i] for i in x['indices']),'subset generators')
        lengths.append(verify_walk(gs,x['witness']))

    expected_rep=[]
    for j,pi in enumerate(PRIMES):
        others=tuple(p for i,p in enumerate(PRIMES) if i!=j)
        for a in divs:
            if canon(a)==canon(pi):continue
            if divisible(a,pi):
                expected_rep.append((j,a,others+(a,)))
    reps=d['proper_subideal_replacement_failures']
    got=[(x['prime_index'],tuple(x['replacement']),tuple(tuple(g) for g in x['generators'])) for x in reps]
    require(got==expected_rep,'replacement coverage')
    for x in reps:
        gs=tuple(tuple(g) for g in x['generators'])
        lengths.append(verify_walk(gs,x['witness']))

    print(json.dumps({
      'status':'PASS','divisor_ideals':len(divs),
      'proper_prime_subsets':len(cases),'proper_subideal_replacements':len(reps),
      'failure_witnesses':len(lengths),'total_steps':sum(lengths),
      'max_walk_length':max(lengths),'arithmetic':'exact integer'
    },sort_keys=True))

if __name__=='__main__':main()
