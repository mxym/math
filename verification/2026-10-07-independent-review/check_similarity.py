#!/usr/bin/env python3
"""Differential audit using arrangement vertices, not polygon clipping."""
from fractions import Fraction as F
import argparse, hashlib
import importlib.util, itertools, json, random, pathlib, sys
sys.dont_write_bytecode = True
v = None

def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def direct_member(z,holes):
    # Simple finite integer loop, deliberately independent of floor/ceil formula.
    for l,r in holes:
        for n in range(int(z-r)-3,int(z-l)+4):
            if l+n<z<r+n:return True
    return False

def oracle_density(holes):
    cuts={F(0),F(1)}
    for l,r in holes:
        cuts.add(l-l.numerator//l.denominator)
        cuts.add(r-r.numerator//r.denominator)
    cuts=sorted(cuts)
    return sum((b-a for a,b in zip(cuts,cuts[1:]) if direct_member((a+b)/2,holes)),F(0))

def oracle_cover(points,holes):
    lo=min(F(0),*(min(a,2*a) for a in points))
    hi=max(F(1),*(1+max(a,2*a) for a in points))
    # Each bounded nonempty closed uncovered polytope has a vertex from these lines.
    lines={(F(1),F(0),F(0)),(F(1),F(0),F(1)),(F(0),F(1),F(1)),(F(0),F(1),F(2))}
    for l,r in holes:
        for endpoint in (l,r):
            for n in range(int(lo-endpoint)-3,int(hi-endpoint)+4):
                b=endpoint+n
                if lo<=b<=hi:
                    for a in points:lines.add((F(1),a,b))
    for (a,b,c),(d,e,f) in itertools.combinations(lines,2):
        det=a*e-b*d
        if not det:continue
        x=(c*e-b*f)/det;t=(a*f-c*d)/det
        if 0<=x<=1 and 1<=t<=2 and all(not direct_member(x+t*p,holes) for p in points):
            return False,{'x':str(x),'t':str(t)}
    return True,None

def main():
    global v
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo-root',type=pathlib.Path,default=pathlib.Path(__file__).resolve().parents[2])
    parser.add_argument('--output',type=pathlib.Path,default=pathlib.Path(__file__).resolve().parent/'results/similarity.json')
    args=parser.parse_args()
    source=args.repo_root/'preprints/004-log-density-similarity/v1.1/verification/check_cover.py'
    expected='9595f9f2db8e4b25f62a7e6932a97d26652232de8f1611acd9a6dc648a16af01'
    require(hashlib.sha256(source.read_bytes()).hexdigest()==expected,'Source differs from audited snapshot')
    spec=importlib.util.spec_from_file_location('subject',source)
    v=importlib.util.module_from_spec(spec); spec.loader.exec_module(v)
    rng=random.Random(20261007)
    cases=[]
    # Boundary-heavy, rational grid data, signed points, wraparound and overlapping holes.
    for k in range(1000):
        points=sorted({F(rng.randint(-4,8),rng.choice((2,4,8))) for _ in range(rng.randint(1,4))})
        holes=[]
        for _ in range(rng.randint(0,4)):
            l=F(rng.randint(-8,8),rng.choice((2,4,8)))
            r=l+F(rng.randint(1,12),rng.choice((4,8,16)))
            holes.append((l,r))
        data={'points':list(map(str,points)),'holes':[[str(a),str(b)] for a,b in holes]}
        observed=v.check(data)
        rho=oracle_density(holes)
        valid,witness=oracle_cover(points,holes)
        require(F(observed['density'])==rho,('density mismatch',data,observed,rho))
        require(observed['valid']==valid,('coverage mismatch',data,observed,witness))
        if not observed['valid']:
            x=F(observed['witness']['x']);t=F(observed['witness']['t'])
            require(0<=x<=1 and 1<=t<=2,'Witness outside rectangle')
            require(all(not direct_member(x+t*a,holes) for a in points),'Witness is covered')
        cases.append(valid)
    result={'status':'PASS','seed':20261007,'cases':len(cases),'true_covers':sum(cases),'uncovered_cases':len(cases)-sum(cases),'oracle':'exact rational arrangement vertices plus independent periodic membership and measure partition','scope':'finite supplied certificates only; not a proof of the main theorem or a constructed low-density blocker'}
    result['subject_sha256']=expected
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()
