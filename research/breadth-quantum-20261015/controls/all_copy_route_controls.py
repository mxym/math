"""Portable exact checks for an all-copy route obstruction and map algebra.
The full physical NPT existence problem remains unresolved.
Usage: python all_copy_route_controls.py --output NEW_EVIDENCE.json
"""
from pathlib import Path
import argparse,itertools,json,datetime,math
from fractions import Fraction as Fr
import sympy as sp
ap=argparse.ArgumentParser();ap.add_argument('--output',required=True);args=ap.parse_args()
target=Path(args.output).resolve();assert not target.exists(),'choose a fresh output path'
def parity_ghz_expect(k,eps):
    # P=I+|00><11|+|11><00|. Each party has a normalized GHZ.
    # Four total support strings allow exact direct contraction at all tested k.
    rows=[((0,0),1),((0,1),-1),((1,0),1),((1,1),-1)]
    def entry(x,y):
        if x==y:return 1-eps
        return Fr(1) if (x,y) in [((0,0),(1,1)),((1,1),(0,0))] else Fr(0)
    return sum(Fr(s*t,4)*entry(x,y)**k for x,s in rows for y,t in rows)
checks=[]
for eps in [Fr(1,10),Fr(1,4),Fr(1,256)]:
    first=1
    while (1-eps)**first>=Fr(1,2):first+=1
    for k in set([1,2,3,first-1,first,first+1]):
        direct=parity_ghz_expect(k,eps);formula=(1-eps)**k-Fr(1,2);assert direct==formula
    assert parity_ghz_expect(first,eps)<0 and parity_ghz_expect(first-1,eps)>=0
    checks.append({'epsilon':str(eps),'first_negative_k_for_this_witness':first,'formula':'(1-epsilon)^k-1/2','direct_four_support_entry_checks':True})
assert parity_ghz_expect(7,Fr(1,10))==-Fr(217031,10000000)

# Self-partial-transpose orthogonally covariant single-site candidate algebra.
# These are known map coordinates; no all-copy property follows from them.
eps=sp.Symbol('epsilon',real=True);orth=[]
for d in [2,3,4]:
    I=sp.eye(d*d);F=sp.zeros(d*d);om=sp.zeros(d*d,1)
    for i,j in itertools.product(range(d),repeat=2):F[d*i+j,d*j+i]=1
    for i in range(d):om[d*i+i]=1
    J=(1-eps)*I-(F+om*om.T)/(d+1)
    PT=sp.Matrix(d*d,d*d,lambda r,c:J[(r//d)*d+c%d,(c//d)*d+r%d])
    assert PT==J and sp.simplify((J*om)[0]+eps)==0
    assert J*om==-eps*om
    rank_controls=[]
    for r in range(1,d+1):
        z=sp.zeros(d*d,1)
        for i in range(r):z[d*i+i]=1
        val=sp.simplify((z.T*J*z)[0]/r)
        assert sp.simplify(val-((1-eps)-sp.Rational(r+1,d+1)))==0
        rank_controls.append({'Schmidt_rank':r,'attaining_expectation':str(val)})
    orth.append({'d':d,'partial_transpose_invariant':True,'maximally_entangled_eigenvalue':'-epsilon','exact_rank_r_minimum':'1-epsilon-(r+1)/(d+1)','attaining_rank_r_vectors':rank_controls,'all_copy_property_proved':False})

out={'schema':'all-copy-route-obstruction-and-single-site-algebra-v1','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'UPB_construction_source':'https://arxiv.org/abs/1502.05630','exact_GHZ_obstruction':checks,'orthogonal_family_source':'https://link.springer.com/article/10.1007/s11128-024-04361-6','orthogonal_single_site_controls':orth,'interpretation':'The specific embedded-qubit finite-n map construction fails at a finite k for every fixed epsilon>0. No general UPB, all-map, or physical NPT impossibility conclusion is claimed. The orthogonal family has only single-site properties verified here.','complete_target_solved':False,'new_major_results':0}
target.parent.mkdir(parents=True,exist_ok=True);target.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'output':str(target),'exact_assertions_passed':True,'complete_target_solved':False}))
