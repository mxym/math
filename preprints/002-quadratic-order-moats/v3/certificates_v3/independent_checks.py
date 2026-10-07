"""Bounded independent checks, not proof or formal verification.
No imports from either certificate producer/verifier.
"""
import json, math
from pathlib import Path
from collections import deque
BASE=Path(__file__).resolve().parent

def is_prime(n):
    return type(n) is int and n>=2 and all(n%d for d in range(2,math.isqrt(n)+1))

def check_bundle(path):
    bundle=json.loads(path.read_text());d=bundle['data'];c=bundle['certificate']
    u,v=d['u'],d['v'];generators=d['generators'];Q=1
    for g in generators:
        a,b=g['alpha'];p=g['p'];assert is_prime(p)
        assert abs(a*a+u*a*b-v*b*b)==p
        Q=math.lcm(Q,p)
    assert Q==c['Q']
    # Test divisibility by solving multiplication via BOTH adjugate coordinates.
    # Thus no reuse of the production code's chosen single kernel row.
    def divisible(x,g):
        a,b=g['alpha'];p=g['p'];s,t=x
        return ((a+u*b)*s-v*b*t)%p==0 and (-b*s+a*t)%p==0
    allowed={(s,t) for s in range(Q) for t in range(Q)
             if all(not divisible((s,t),g) for g in generators)}
    h={tuple(row[:2]):tuple(row[2:]) for row in c['potentials']}
    assert len(h)==len(c['potentials']) and set(h)==allowed
    # Independently realize every quotient component as ACTUAL integer vertices.
    unseen=set(allowed);sizes=[];directed=0
    while unseen:
        root=unseen.pop();queue=deque([root]);reps={root};vertices={root}
        while queue:
            r=queue.popleft();x=tuple(r[i]+Q*(h[r][i]-h[root][i]) for i in range(2))
            for step in d['steps']:
                y=tuple(x[i]+step[i] for i in range(2));s=tuple(z%Q for z in y)
                if s not in allowed:continue
                directed+=1
                expected=tuple(s[i]+Q*(h[s][i]-h[root][i]) for i in range(2))
                assert y==expected
                if s not in reps:
                    reps.add(s);vertices.add(y);unseen.remove(s);queue.append(s)
        assert len(vertices)==len(reps)
        sizes.append(len(reps))
    return dict(file=str(path.relative_to(BASE)),Q=Q,allowed=len(allowed),
                directed_edges=directed,component_sizes=sorted(sizes),max_component=max(sizes,default=0))

if __name__=='__main__':
    results=[check_bundle(BASE/f'{name}.json') for name in
             ('gaussian_four_steps','sqrt2_four_steps','gaussian_eight_steps','sqrt2_eight_steps')]
    print(json.dumps(results,indent=2))
