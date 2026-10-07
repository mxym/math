"""Reproducible checks, tampering tests, and separate adjugate/lift audit."""
import copy
import json
from pathlib import Path
import prime_element_checker as checker

HERE=Path(__file__).parent

def independent_audit(bundle):
    """No checker functions: both adjugate coordinates test exact divisibility.
    Every lifted representative's step-neighbors must lie in its finite lifted
    component, including wraps. Independently counts those lifted components.
    """
    from math import gcd,isqrt
    data,certificate=bundle['data'],bundle['certificate']
    u,v=data['u'],data['v'];Q=1
    for g in data['generators']:
        p=g['p'];a,b=g['alpha']
        assert p>=2 and all(p%d for d in range(2,isqrt(p)+1))
        assert abs(a*a+u*a*b-v*b*b)==p
        Q=Q*p//gcd(Q,p)
    assert Q==certificate['Q']
    allowed=set()
    for x in range(Q):
        for y in range(Q):
            excluded=False
            for g in data['generators']:
                a,b=g['alpha'];p=g['p']
                # alpha^{-1}(x+y omega) lies in O iff BOTH numerators divide by p.
                if ((a+u*b)*x-v*b*y)%p==0 and (-b*x+a*y)%p==0:
                    excluded=True
            if not excluded:allowed.add((x,y))
    rows=certificate['potentials'];h={(r[0],r[1]):(r[2],r[3]) for r in rows}
    assert len(h)==len(rows) and set(h)==allowed
    lifted={(x+Q*h[(x,y)][0],y+Q*h[(x,y)][1]) for x,y in allowed}
    # A valid certificate may choose different gauge in separate components;
    # its union of lifted finite components is still closed under allowed steps.
    adjacency={x:[] for x in lifted}
    for x in lifted:
        for dx,dy in data['steps']:
            y=(x[0]+dx,x[1]+dy)
            if (y[0]%Q,y[1]%Q) in allowed:
                assert y in lifted, ('Unclosed finite lift',x,y)
                adjacency[x].append(y)
    unseen=set(lifted);sizes=[]
    while unseen:
        todo=[unseen.pop()];size=0
        while todo:
            x=todo.pop();size+=1
            for y in adjacency[x]:
                if y in unseen:unseen.remove(y);todo.append(y)
        sizes.append(size)
    result=(len(allowed),sum(map(len,adjacency.values())),sorted(sizes))
    s=bundle['statistics']
    assert result==(s['allowed_residues'],s['directed_edges'],s['quotient_component_sizes'])
    return result

count=0

def check(condition):
    global count
    assert condition
    count+=1

def rejected(call):
    try:call()
    except (ValueError,KeyError,TypeError):return True
    return False

for name in ['gaussian_four_steps','sqrt2_four_steps','gaussian_eight_steps','sqrt2_eight_steps']:
    bundle=json.loads((HERE/(name+'.json')).read_text())
    check(checker.verify_certificate(bundle['data'],bundle['certificate']))
    check(independent_audit(bundle)[0]>0)
    check(checker.statistics(bundle['data'],bundle['certificate'])==bundle['statistics'])
    if name.startswith('gaussian'):
        selected={g['p'] for g in bundle['data']['generators']};M=max(selected)
        exact=sum(a*a+b*b in selected for a in range(-M,M+1) for b in range(-M,M+1))
        check(exact==bundle['statistics']['finite_exception_count'])
        expected=20 if name=='gaussian_four_steps' else 92820
        check(bundle['statistics']['finite_exception_component_bound']==expected)
    else:
        expected=179200 if name=='sqrt2_four_steps' else 351232
        check(bundle['statistics']['irreducible_component_bound']==expected)

real=json.loads((HERE/'sqrt2_four_steps.json').read_text())
d,c=real['data'],real['certificate']
for mutate in [lambda x:x.update(Q=7),lambda x:x['potentials'].pop(),
               lambda x:x['potentials'].append(x['potentials'][0]),
               lambda x:x['potentials'][0].__setitem__(2,x['potentials'][0][2]+1),
               lambda x:x['potentials'][0].__setitem__(0,-1),
               lambda x:x.update(format='quadratic-split-pair-old'),
               lambda x:x['potentials'][0].__setitem__(2,True)]:
    bad=copy.deepcopy(c);mutate(bad)
    check(rejected(lambda:checker.verify_certificate(d,bad)))
for mutate in [lambda x:x.update(v=1),lambda x:x['generators'][1].update(p=9),
               lambda x:x['generators'][1].update(alpha=[3,2]),
               lambda x:x['steps'].pop(),lambda x:x['steps'].append([0,0]),
               lambda x:x.update(u=True),lambda x:x.update(steps=x['steps']*17)]:
    bad=copy.deepcopy(d);mutate(bad)
    check(rejected(lambda:checker.prepare(bad)))
empty=dict(format=checker.FORMAT,u=0,v=2,generators=[],steps=[])
check(checker.statistics(empty,checker.make_certificate(empty))['irreducible_component_bound']==1)
line=dict(empty,steps=[[1,0],[-1,0]])
check(checker.make_certificate(line) is None)
# Ramification alone in Z[sqrt2] leaves infinite vertical lines.
partial=copy.deepcopy(d);partial['generators']=partial['generators'][:1]
check(checker.make_certificate(partial) is None)
# Permitted same-residue steps force nonzero voltage, and must be rejected.
same=copy.deepcopy(d);same['steps']=[[14,0],[-14,0]]
check(checker.make_certificate(same) is None)
# Same rational prime can have either identical or distinct repeated kernels.
for extra in [{'p':7,'alpha':[3,-1]},{'p':7,'alpha':[3,1]}]:
    extended=copy.deepcopy(d);extended['generators'].append(extra)
    check(checker.verify_certificate(extended,checker.make_certificate(extended)))
    # Neither additional generator introduces a new norm value.
    # Its avoiding components still have maximum size six.
    check(checker.statistics(extended,checker.make_certificate(extended))['irreducible_component_bound']==179200)
# The cell budget is enforced before enumeration.
large=dict(format=checker.FORMAT,u=0,v=-1,steps=[],generators=[{'p':65537,'alpha':[256,1]}])
check(rejected(lambda:checker.prepare(large)))
print(f'{count} checks passed, including four independently reconstructed finite lifts.')
