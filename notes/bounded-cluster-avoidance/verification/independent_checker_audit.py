#!/usr/bin/env python3
"""Independent rational oracle: arrangement gaps and Fourier--Motzkin.

No clipping routine, gap-merging routine, or density routine is imported from
the subject checker. Only its public `check` function is called for comparison.
These are finite regressions, never certificates for arbitrarily small density.
"""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import importlib.util
import json
import random

ROOT = Path(__file__).resolve().parent
SUBJECT = ROOT
spec = importlib.util.spec_from_file_location('subject_checker', SUBJECT/'check_cluster_cover.py')
subject = importlib.util.module_from_spec(spec)
spec.loader.exec_module(subject)

def floor(z):
    return z.numerator//z.denominator

def inside(z, holes):
    # Enumerate the few relevant translates directly, using strict inequalities.
    return any(a+n < z < b+n
               for a,b in holes
               for n in range(floor(z-b)-1, floor(z-a)+2))

def endpoints(holes, lo, hi):
    vals={lo,hi}
    for a,b in holes:
        for n in range(floor(lo-b)-2, floor(hi-a)+3):
            vals.update(z for z in (a+n,b+n) if lo <= z <= hi)
    return sorted(vals)

def oracle_density(holes):
    cuts=endpoints(holes,F(0),F(1))
    return sum((b-a for a,b in zip(cuts,cuts[1:]) if inside((a+b)/2,holes)),F(0))

def oracle_gaps(holes,lo,hi):
    cuts=endpoints(holes,lo,hi)
    # We may split a connected closed gap into pieces. Completeness is preserved.
    out=[(z,z) for z in cuts if not inside(z,holes)]
    for a,b in zip(cuts,cuts[1:]):
        if not inside((a+b)/2,holes):
            assert not inside(a,holes) and not inside(b,holes)
            out.append((a,b))
    return out

def feasible(strips):
    # Strip L <= x+a*t <= U. Add 0 <= x <= 1.
    lowers=[(F(0),F(0))]+[(L,-a) for a,L,U in strips]
    uppers=[(F(1),F(0))]+[(U,-a) for a,L,U in strips]
    tl,tu=F(1),F(2)
    for L,ls in lowers:
        for U,us in uppers:
            # L+ls*t <= U+us*t, after eliminating x.
            coef=ls-us; rhs=U-L
            if coef > 0: tu=min(tu,rhs/coef)
            elif coef < 0: tl=max(tl,rhs/coef)
            elif rhs < 0: return None
            if tl > tu: return None
    return max(L+s*tl for L,s in lowers),tl

def oracle(data):
    clusters=[list(zip(map(F,row['points']),map(F,row.get('radii',['0']*len(row['points'])))))
              for row in data['clusters']]
    holes=[tuple(map(F,row)) for row in data['holes']]
    rho=oracle_density(holes)
    if rho > F(data.get('max_density','1')):
        return False,rho,None
    lo=min(a-r for row in clusters for a,r in row)
    hi=max(1+2*a+r for row in clusters for a,r in row)
    gaps=oracle_gaps(holes,lo,hi)
    alternatives=[[(a,l-r,u+r) for a,r in row for l,u in gaps] for row in clusters]
    stack=[(0,())]
    while stack:
        index,strips=stack.pop()
        pt=feasible(strips)
        if pt is None:continue
        if index == len(alternatives):
            return False,rho,pt
        stack.extend((index+1,strips+(strip,)) for strip in alternatives[index])
    return True,rho,None

def main():
    rng=random.Random(20261007)
    data=json.loads((SUBJECT/'toy_cluster_certificate.json').read_text())
    cases=[('four_cluster_toy',data)]
    cases.append(('six_cluster_three_quarters_toy',json.loads((SUBJECT/'toy_cluster_certificate_3_4.json').read_text())))
    cases.append(('three_cluster_deletion',{**data,'clusters':data['clusters'][:3]}))
    cases += [
      ('full_measure_singleton_gap',{'clusters':[{'points':['1/8']}],
                                    'holes':[['0','1/2'],['1/2','1']]}),
      ('large_errors_full_hole',{'clusters':[{'points':['1/8','1/4'],'radii':['2','3']}],
                                 'holes':[['-1/10','11/10']]}),
      ('wrapped_touching',{'clusters':[{'points':['1/8','1/4']},{'points':['3/8']}],
                           'holes':[['-1/2','0'],['0','1/2']]}),
    ]
    for n in range(400):
        clusters=[]
        for j in range(rng.randint(1,3)):
            count=rng.randint(1,3)
            clusters.append({'points':[str(F(rng.randint(1,16),16)) for _ in range(count)],
                             'radii':[str(F(rng.randint(0,3),32)) for _ in range(count)]})
        holes=[]
        for _ in range(rng.randint(0,3)):
            a=F(rng.randint(-8,16),16); b=a+F(rng.randint(1,24),16)
            holes.append([str(a),str(b)])
        cases.append((f'random_{n}',{'clusters':clusters,'holes':holes,
                                      'max_density':str(F(rng.randint(0,8),8))}))
    # Geometry-focused tests never exit early on a density-budget mismatch.
    # Vary relative errors, annular levels, shifted holes, split/touching gaps.
    for n in range(600):
        eta=F(rng.randint(0,20),100)
        count=rng.randint(2,5)
        start=rng.randint(1,3)
        clusters=[]
        for j in range(start,start+count):
            a=F(1,2**j)
            points=[a,F(3,2)*a]
            clusters.append({'points':list(map(str,points)),
                             'radii':[str(eta*a) for a in points]})
        shift=F(rng.randint(-8,8),16)
        length=F(rng.randint(10,16),16)
        if n%3 == 0:
            holes=[[str(shift),str(shift+length)]]
        elif n%3 == 1:
            mid=shift+length/2
            holes=[[str(shift),str(mid)],[str(mid),str(shift+length)]]
        else:
            mid=shift+length/2
            holes=[[str(shift),str(mid-F(1,64))],[str(mid+F(1,64)),str(shift+length)]]
        cases.append((f'geometry_{n}',{'clusters':clusters,'holes':holes,'max_density':'1'}))
    covers=failures=budget_failures=0; rows=[]
    for name,data in cases:
        got=subject.check(data); valid,rho,pt=oracle(data)
        if (got['valid'],F(got['density'])) != (valid,rho):
            raise ArithmeticError(f'Disagreement {name}: {data}, {got}, {(valid,rho,pt)}')
        covers+=valid;failures+=not valid
        budget_failures+=got.get('reason') == 'density budget exceeded'
        if not name.startswith(('random_','geometry_')):
            rows.append({'name':name,'valid':valid,'density':str(rho),
                         'oracle_counterexample':None if pt is None else list(map(str,pt)),
                         'subject_result':got})
    report={'status':'PASS','exact_arithmetic':'Fraction',
            'cases':len(cases),'covers':covers,'failures':failures,
            'density_budget_failures':budget_failures,
            'geometric_feasibility_cases':len(cases)-budget_failures,
            'independent_method':'Fourier--Motzkin elimination and midpoint arrangement density/gaps',
            'selected_cases':rows,
            'scope':'Finite checker audit, not a global small-density construction'}
    (ROOT/'independent_checker_results.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__':main()
