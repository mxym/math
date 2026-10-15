"""Exact rational controls of the fractional formulation, not SC0 resolution."""
from fractions import Fraction
from functools import reduce
from itertools import product
from math import gcd, lcm
from pathlib import Path
import json
import z3
from finite_decoder import samples
from resumed_controls import WARMUTH

HERE=Path(__file__).parent

def transform(n,a,b,mult,add,flip):
    aa=0; bb=0
    for i in range(n):
        if (a>>i)&1:
            j=(mult*i+add)%n
            aa|=1<<j
            bb|=((((b>>i)&1)^flip)<<j)
    return aa,bb

def triangle():
    n=3; C=[1,2,4]; S=samples(n,C)
    P={(0,0):[(7,Fraction(1))]}
    for i in range(3):
        P[(1<<i,1<<i)]=[(1<<i,Fraction(1))]
        P[(1<<i,0)]=[(0,Fraction(1,2)),(7^(1<<i),Fraction(1,2))]
    coverage=[]
    for a,b in S:
        value=sum((mass for (u,lab),options in P.items()
                   if not(u&~a) and lab==(b&u)
                   for h,mass in options if h&a==b),Fraction())
        if value<1:
            raise ValueError('Fractional triangle point fails full sample coverage')
        coverage.append({'mask':a,'labels':b,'coverage':str(value)})
    integer=[x for x in product([0,1],repeat=3)
             if all(x[i]+x[j]>=1 for i,j in [(0,1),(1,2),(0,2)])]
    return {'C':C,'n':n,'VC':1,'compression_bound':1,
            'fractional_x':['1/2']*3,'tight_triangle_matrix_determinant':2,
            'minimum_integer_cost':min(sum(x) for x in integer),
            'fractional_cost':'3/2','full_partial_sample_coverage':coverage,
            'scope':'A fractional vertex on an explicitly restricted face, not infeasibility of the original compression problem.'}

def warmuth_dual():
    n=5; C=sorted(WARMUTH); S=samples(n,C); allS=set(S)
    group=[(a,b,int(a in [2,3])) for a in [1,2,3,4] for b in range(5)]
    if len(group)!=20 or any({transform(n,31,c,*g)[1] for c in C}!=set(C) for g in group):
        raise ValueError('Claimed group does not preserve the complete class')
    orbits=[]; used=set()
    for s in S:
        if s in used:
            continue
        orbit={transform(n,*s,*g) for g in group}
        if not orbit<=allS:
            raise ValueError('Sample orbit leaves the full sample complex')
        orbits.append(sorted(orbit)); used|=orbit
    index={s:j for j,orbit in enumerate(orbits) for s in orbit}
    weight=[z3.Real(f'w{j}') for j in range(len(orbits))]
    y0,y1=z3.Reals('y0 y1')
    solver=z3.Solver(); solver.set(timeout=30000)
    solver.add(*[w>=0 for w in weight],y0>=0,y1>=0)
    def score(h,T):
        u,lab=T
        return z3.Sum([weight[index[(a,b)]] for a,b in S
                       if not(u&~a) and b&u==lab and h&a==b])
    for h in range(32):
        solver.add(y0>=score(h,(0,0)))
        if not(h&1):
            solver.add(y1>=score(h,(1,0)))
    solver.add(z3.Sum([len(orbit)*w for orbit,w in zip(orbits,weight)])>=y0+10*y1+1)
    sat=solver.check()
    if sat!=z3.sat:
        return {'status':str(sat),'scope':'Dual discovery only; no zero-error scheme conclusion.'}
    model=solver.model()
    ww=[Fraction(str(model.eval(w,model_completion=True))) for w in weight]
    scale=lcm(*(w.denominator for w in ww))
    ii=[int(w*scale) for w in ww]
    common=reduce(gcd,ii)
    if common:
        ii=[w//common for w in ii]
    weights={s:ii[index[s]] for s in S}
    # Independent ordinary-integer verification over EVERY total hypothesis
    # for each of the 11 messages, not just group representatives.
    messages=[s for s in S if s[0].bit_count()<=1]
    capacities=[]
    for u,lab in messages:
        values=[(sum(weights[(a,b)] for a,b in S
                     if not(u&~a) and b&u==lab and h&a==b),h)
                for h in range(32) if h&u==lab]
        maximum,h=max(values)
        capacities.append({'message_mask':u,'message_labels':lab,
                           'maximum_weighted_coverage':maximum,'maximizing_hypothesis':h})
    left=sum(weights.values()); right=sum(r['maximum_weighted_coverage'] for r in capacities)
    if not all(w>=0 for w in weights.values()) or left<=right:
        raise ValueError('Discovered weights are not a legal exact dual obstruction')
    return {'status':'exact_integer_dual_verified','n':5,'C':C,'actual_VC':2,
            'attempted_compression_size':1,'left_total_sample_weight':left,
            'right_total_message_capacity':right,'strict_gap':left-right,
            'nonzero_sample_weights':[{'mask':a,'labels':b,'weight':w} for (a,b),w in weights.items() if w],
            'all_11_message_capacities':capacities,
            'support_orbits':[{'weight':w,'samples':[list(s) for s in orbit]} for orbit,w in zip(orbits,ii) if w],
            'scope':'Fractional impossibility only BELOW VC=2. Not SC0 counterexample. Exact integer dual checking does not trust a solver UNSAT report.'}

if __name__=='__main__':
    record={'triangle':triangle(),'warmuth_lower_size_dual':warmuth_dual(),
            'scope':'Only exact finite controls of the stated auxiliary lemmas, not an independent mathematical review or the original universal conjecture.'}
    (HERE/'FRACTIONAL_CONTROLS.json').write_text(json.dumps(record,indent=2)+'\n')
    print(json.dumps({k:({a:b for a,b in v.items() if a not in ['full_partial_sample_coverage','nonzero_sample_weights','support_orbits','all_11_message_capacities']} if isinstance(v,dict) else v) for k,v in record.items()},indent=2))
