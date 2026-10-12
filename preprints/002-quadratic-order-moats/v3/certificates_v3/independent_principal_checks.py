"""Independent finite principal-ideal checks by enumerating MULTIPLICATION images.
Does not import either checker and does not use adjugate membership tests.
"""
import json, math
from pathlib import Path
from collections import deque
BASE=Path(__file__).resolve().parent

def independent_prepare(data):
    u,v=data['u'],data['v'];periods=[];gens=[]
    for entry in data['generators']:
        a,b=entry['alpha'];D=abs(a*a+u*a*b-v*b*b);assert D>=2
        # Recover minimal scalar period directly in O/D O, independently of D/g.
        image={( (a*x+v*b*y)%D,(b*x+(a+u*b)*y)%D)
               for x in range(D) for y in range(D)}
        period=next(t for t in range(1,D+1) if (t%D,0) in image and (0,t%D) in image)
        assert period==D//math.gcd(a,b)
        periods.append(period);gens.append((a,b,D))
    Q=math.lcm(*periods) if periods else 1
    forbidden=set()
    for a,b,D in gens:
        forbidden.update(((a*x+v*b*y)%Q,(b*x+(a+u*b)*y)%Q)
                         for x in range(Q) for y in range(Q))
    allowed={(x,y) for x in range(Q) for y in range(Q)}-forbidden
    return Q,allowed,periods

def positive():
    bundle=json.loads((BASE/'gaussian_eight_steps_principal.json').read_text());d=bundle['data'];c=bundle['certificate']
    Q,allowed,periods=independent_prepare(d);assert c['Q']==Q
    h={tuple(r[:2]):tuple(r[2:]) for r in c['potentials']};assert set(h)==allowed and len(h)==len(c['potentials'])
    unseen=set(allowed);sizes=[];directed=0
    while unseen:
        root=unseen.pop();todo=deque([root]);size=0
        while todo:
            r=todo.popleft();size+=1
            x=tuple(r[i]+Q*(h[r][i]-h[root][i]) for i in range(2))
            for step in d['steps']:
                y=tuple(x[i]+step[i] for i in range(2));s=tuple(t%Q for t in y)
                if s not in allowed:continue
                directed+=1
                assert y==tuple(s[i]+Q*(h[s][i]-h[root][i]) for i in range(2))
                if s in unseen:unseen.remove(s);todo.append(s)
        sizes.append(size)
    return dict(case='positive',Q=Q,periods=periods,allowed=len(allowed),directed=directed,components=len(sizes),max_component=max(sizes))

def negative():
    b=json.loads((BASE/'gaussian_eight_steps_principal_rejected.json').read_text());d=b['data'];Q,allowed,periods=independent_prepare(d)
    assert Q==b['Q'] and len(allowed)==b['allowed_residues']
    witness=b['nonzero_voltage_walk'];root=tuple(witness['root']);x=root
    assert tuple(t%Q for t in x) in allowed
    for step in witness['steps']:
        assert step in d['steps'];x=tuple(x[i]+step[i] for i in range(2))
        assert tuple(t%Q for t in x) in allowed
    displacement=tuple(x[i]-root[i] for i in range(2))
    assert displacement!=(0,0) and all(t%Q==0 for t in displacement)
    return dict(case='negative',Q=Q,periods=periods,allowed=len(allowed),walk_steps=len(witness['steps']),displacement=displacement)

if __name__=='__main__':print(json.dumps([positive(),negative()],indent=2))
