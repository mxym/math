"""Tests for the separate principal-ideal format. Run without -O."""
import copy
import json
from pathlib import Path
from math import gcd,lcm
import principal_ideal_checker as c

HERE=Path(__file__).parent
count=0

def check(value):
    global count
    assert value
    count+=1

def rejects(call):
    try:call()
    except (ValueError,KeyError,TypeError):return True
    return False

def inside(x,alpha,u,v):
    a,b=alpha;det=a*a+u*a*b-v*b*b
    n1=(a+u*b)*x[0]-v*b*x[1]
    n2=-b*x[0]+a*x[1]
    return n1%det==0 and n2%det==0

def audit_walk(bundle):
    d=bundle['data'];w=bundle['nonzero_voltage_walk'];Q=bundle['Q']
    u,v=d['u'],d['v'];x=tuple(w['root']);start=x
    generators=[g['alpha'] for g in d['generators']]
    periods=[abs(a*a+u*a*b-v*b*b)//gcd(a,b) for a,b in generators]
    assert Q==lcm(*periods)
    F={tuple(x) for x in d['steps']}
    assert all(not inside(x,g,u,v) for g in generators)
    for step in w['steps']:
        assert tuple(step) in F
        x=(x[0]+step[0],x[1]+step[1])
        assert all(not inside(x,g,u,v) for g in generators)
    displacement=(x[0]-start[0],x[1]-start[1])
    assert displacement!=(0,0)
    assert list(displacement)==w['total_displacement']
    assert all(displacement[i]==Q*w['voltage'][i] for i in range(2))
    return True

positive=json.loads((HERE/'gaussian_eight_steps_principal.json').read_text())
negative=json.loads((HERE/'gaussian_eight_steps_principal_rejected.json').read_text())
check(c.verify_certificate(positive['data'],positive['certificate']))
check(c.statistics(positive['data'],positive['certificate'])==positive['statistics'])
# Independently reconstruct full allowed set and closure of the supplied lift.
d=positive['data'];Q=positive['certificate']['Q'];u,v=d['u'],d['v']
allowed={(a,b) for a in range(Q) for b in range(Q)
         if all(not inside((a,b),g['alpha'],u,v) for g in d['generators'])}
h={tuple(r[:2]):tuple(r[2:]) for r in positive['certificate']['potentials']}
check(set(h)==allowed)
lifted={(a+Q*h[(a,b)][0],b+Q*h[(a,b)][1]) for a,b in allowed}
closed=True
for x in lifted:
    for da,db in d['steps']:
        y=(x[0]+da,x[1]+db)
        if (y[0]%Q,y[1]%Q) in allowed and y not in lifted:closed=False
check(closed)
check(c.make_certificate(negative['data']) is None)
check(audit_walk(negative))
check(negative['nonzero_voltage_walk']['total_displacement']==[30,0])
check(len(negative['nonzero_voltage_walk']['steps'])==38)
# A malformed claimed displacement or a forbidden/unsupported step is rejected.
for mutate in [lambda b:b['nonzero_voltage_walk'].update(total_displacement=[0,0]),
               lambda b:b['nonzero_voltage_walk']['steps'][0].__setitem__(0,20)]:
    bad=copy.deepcopy(negative);mutate(bad)
    try:audit_walk(bad)
    except AssertionError:check(True)
    else:check(False)
base=dict(format=c.FORMAT,u=0,v=-1,steps=[],generators=[{'alpha':[3,0]}])
Q,F,A=c.prepare(base)
check(Q==3 and len(A)==8 and (0,0) not in A)
# Both adjugate rows matter: rational 3 divides precisely pairs with both entries divisible by 3.
check((0,1) in A and (1,0) in A)
check(c.verify_certificate(base,c.make_certificate(base)))
# Composite reducible generator 2 is allowed too; its scalar period is 2, not its norm4.
b=copy.deepcopy(base);b['generators']=[{'alpha':[2,0]}]
Q,F,A=c.prepare(b)
check(Q==2 and len(A)==3)
for alpha in [[0,0],[1,0],[-1,0],[0,1]]:
    b=copy.deepcopy(base);b['generators']=[{'alpha':alpha}]
    check(rejects(lambda:c.prepare(b)))
# Nonprimitive, non-rational generator: 2+2i has norm8, content2, period4.
b=copy.deepcopy(base);b['generators']=[{'alpha':[2,2]}]
Q,F,A=c.prepare(b)
check(Q==4 and len(A)==14)
check(all(inside((Q*a,Q*b),[2,2],0,-1) for a,b in [(1,0),(0,1)]))
check(not inside((2,0),[2,2],0,-1))
# Restore strict bounds and explicit format separation.
b=copy.deepcopy(base);b['generators']=[{'alpha':[257,0]}]
check(rejects(lambda:c.prepare(b)))
b=copy.deepcopy(positive['certificate']);b['format']='quadratic-prime-element-sieve-v1'
check(rejects(lambda:c.verify_certificate(positive['data'],b)))
b=copy.deepcopy(positive['certificate']);b['potentials'].pop()
check(rejects(lambda:c.verify_certificate(positive['data'],b)))
print(f'{count} principal-ideal checks passed, including positive finite lift and explicit Q30 rejection walk.')
