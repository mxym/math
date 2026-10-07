#!/usr/bin/env python3
import json,math,sys
from math import isqrt
from pathlib import Path

F8={(a,b) for a in (-1,0,1) for b in (-1,0,1) if (a,b)!=(0,0)}

def require(c,m):
    if not c: raise ValueError(m)

def prime_factors(n):
    out=[];p=2
    while p*p<=n:
        if n%p==0:
            out.append(p)
            while n%p==0:n//=p
        p=3 if p==2 else p+2
    if n>1:out.append(n)
    return out

def squarefree(n): return n==math.prod(prime_factors(n))

def sumsq_prime(p):
    for a in range(1,isqrt(p)+1):
        b2=p-a*a;b=isqrt(b2)
        if b and b*b==b2:return (a,b)
    raise ValueError('bad split prime')

def expected_generators(q):
    out=[]
    for p in prime_factors(q):
        if p==2:out.append((1,1))
        elif p%4==1:
            a,b=sumsq_prime(p);out += [(a,b),(a,-b)]
        else:out.append((p,0))
    return out

def divisible(z,g):
    x,y=z;a,b=g;D=a*a+b*b
    return (a*x+b*y)%D==0 and (-b*x+a*y)%D==0

def allowed(z,gs): return all(not divisible(z,g) for g in gs)

def verify_failure(c):
    q=c['q']; gs=[tuple(g) for g in c['generators']]
    require(c['rational_primes']==prime_factors(q),'wrong rational prime list')
    require(gs==expected_generators(q),'wrong maximal Gaussian prime generators')
    root=tuple(c['root']);steps=[tuple(d) for d in c['steps']]
    require(all(d in F8 for d in steps),'non-F8 step')
    require(allowed(root,gs),'root forbidden')
    z=root
    seen_res=set()
    for d in steps:
        require(allowed(z,gs),'walk visits forbidden point')
        z=(z[0]+d[0],z[1]+d[1])
        require(allowed(z,gs),'walk enters forbidden point')
        seen_res.add((z[0]%q,z[1]%q))
    dx=z[0]-root[0];dy=z[1]-root[1]
    require(dx%q==0 and dy%q==0,'walk not quotient closed')
    v=(dx//q,dy//q)
    require(v!= (0,0),'zero voltage')
    require(list(v)==c['voltage'],'wrong stored voltage')
    # Independent allowed-residue count.
    cnt=sum(allowed((x,y),gs) for x in range(q) for y in range(q))
    require(cnt==c['allowed_residues'],'wrong allowed-residue count')
    return len(steps)

def main():
    here=Path(__file__).resolve().parent
    data=json.loads((here/'period_optimality.json').read_text())
    require(data['schema']=='mxym-math-002-v4-gaussian-f8-period-optimality-1','schema')
    cases=data['failed_radicals']
    expected=[1]+[q for q in range(2,130) if squarefree(q)]
    require([c['q'] for c in cases]==expected,'incomplete radical coverage')
    lengths=[verify_failure(c) for c in cases]

    # Independently replay the inherited positive q=130 certificate.
    repo=here.parents[3] if here.name=='code' else None
    # v4/code -> v4 -> entry root
    entry=here.parent.parent
    v3=entry/'v3'/'certificates_v3'
    sys.path.insert(0,str(v3))
    from principal_ideal_checker import verify_certificate,statistics,prepare
    bundle=json.loads((v3/'gaussian_eight_steps_principal.json').read_text())
    expected_data={
      'format':'quadratic-principal-ideal-sieve-v1','u':0,'v':-1,
      'steps':[list(x) for x in sorted(F8)],
      'generators':[{'alpha':g} for g in data['positive_generators']]
    }
    # Order of F8 in historical bundle is lexicographic and matches sorted(F8).
    require(bundle['data']==expected_data,'historical positive data mismatch')
    require(verify_certificate(bundle['data'],bundle['certificate']),'positive verification failed')
    Q,_,_=prepare(bundle['data'])
    require(Q==130,'positive period is not 130')
    st=statistics(bundle['data'],bundle['certificate'])
    print(json.dumps({
      'status':'PASS',
      'failed_radicals':len(cases),
      'largest_failed_radical':max(expected),
      'max_failure_walk_length':max(lengths),
      'positive_period':Q,
      'positive_allowed_residues':st['allowed_residues'],
      'positive_avoiding_bound':st['avoiding_bound'],
      'positive_gaussian_component_bound':st['finite_exception_component_bound'],
      'arithmetic':'exact integer'
    },sort_keys=True))

if __name__=='__main__':main()
