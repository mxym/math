"""Bounded negative discovery for full CH via the known TDF/blow-up equivalence."""
import os
os.environ["OMP_NUM_THREADS"]="1"
os.environ["OPENBLAS_NUM_THREADS"]="1"
from pathlib import Path
from fractions import Fraction
from datetime import datetime,timezone
from collections import deque
import random,time,json,math
import numpy as np
from scipy.optimize import linprog

SECONDS=300
SEED=2026101404
rng=random.Random(SEED)
def utc():return datetime.now(timezone.utc).isoformat().replace("+00:00","Z")
def distances(out,start):
    d=[None]*len(out);d[start]=0;q=deque([start])
    while q:
        v=q.popleft()
        for w in out[v]:
            if d[w] is None:d[w]=d[v]+1;q.append(w)
    return d
def girth(out):
    ans=len(out)+1
    for v in range(len(out)):
        ds=distances(out,v)
        for w in range(len(out)):
            if v in out[w] and ds[w] is not None:ans=min(ans,ds[w]+1)
    return ans
def build(n,g,old=None):
    if old is None:out=[{(i+1)%n} for i in range(n)]
    else:
        out=[set(x) for x in old]
        optional=[(i,j) for i in range(n) for j in out[i] if j!=(i+1)%n]
        rng.shuffle(optional)
        for i,j in optional[:rng.randint(1,max(1,len(optional)//3))]:out[i].remove(j)
    arcs=[(i,j) for i in range(n) for j in range(n) if i!=j and j not in out[i]]
    rng.shuffle(arcs)
    for u,v in arcs:
        ds=distances(out,v)
        if ds[u] is None or ds[u]+1>=g:out[u].add(v)
    return out
def exact_primal(a,x):
    w=[max(Fraction(0),Fraction(float(v)).limit_denominator(10**6)) for v in x]
    row=[sum((w[j] for j,v in enumerate(r) if v),Fraction(0)) for r in a]
    if min(row)<=0:return None
    scale=max(Fraction(1),Fraction(1)/min(row))
    w=[v*scale for v in w]
    row=[sum((w[j] for j,v in enumerate(r) if v),Fraction(0)) for r in a]
    assert min(row)>=1 and all(v>=0 for v in w)
    return w,sum(w,Fraction(0))
def exact_dual(a,x):
    y=[max(Fraction(0),Fraction(-float(v)).limit_denominator(10**6)) for v in x]
    col=[sum((y[i] for i in range(len(a)) if a[i][j]),Fraction(0)) for j in range(len(a))]
    scale=max(Fraction(1),max(col))
    y=[v/scale for v in y]
    assert all(sum((y[i] for i in range(len(a)) if a[i][j]),Fraction(0))<=1 for j in range(len(a)))
    return y,sum(y,Fraction(0))
def frac(x):return [x.numerator,x.denominator]
def tr_counts(a,k):
    n=len(a);p=[[int(i==j) for j in range(n)] for i in range(n)];r=[]
    for _ in range(k):
        p=[[sum(p[i][t]*a[t][j] for t in range(n)) for j in range(n)] for i in range(n)]
        r.append(sum(p[i][i] for i in range(n)))
    return r

cells=[(n,g) for g in range(4,9) for n in [13,17,21,25,29,33,41] if n>=g+2]
best={};states={};starts=0;lp_failures=0;certificate=None
began=utc();t0=time.monotonic();last=t0
print(json.dumps({"event":"started","utc":began,"seconds":SECONDS,"scope":"Selected actual saturated Hamiltonian base graphs and mutations; no exhaustive positive coverage."}),flush=True)
while time.monotonic()-t0<SECONDS:
    n,g=cells[starts%len(cells)];key=f"n{n}-g{g}"
    old=states.get(key) if rng.randrange(3) else None
    out=build(n,g,old)
    a=[[int(j in out[i]) for j in range(n)] for i in range(n)]
    res=linprog(np.ones(n),A_ub=-np.array(a,dtype=float),b_ub=-np.ones(n),bounds=(0,None),method="highs")
    starts+=1
    if not res.success:lp_failures+=1;continue
    actual_g=girth(out);assert actual_g>=g
    margin=float(res.fun)-(actual_g-1)
    if key not in best or margin<best[key]["discovery_margin_float"]:
        primal=exact_primal(a,res.x);assert primal is not None
        w,upper=primal;y,lower=exact_dual(a,res.ineqlin.marginals)
        assert lower<=upper
        tr=tr_counts(a,actual_g)
        assert tr[:actual_g-1]==[0]*(actual_g-1) and tr[-1]>0
        best[key]={"n":n,"required_girth":g,"actual_girth":actual_g,"adjacency":a,
                   "row_degrees":list(map(sum,a)),"girth_closed_walk_crosscheck":tr,
                   "discovery_objective_float":float(res.fun),"discovery_margin_float":margin,
                   "rational_primal_weights":[frac(v) for v in w],"certified_primal_upper":frac(upper),
                   "rational_dual_weights":[frac(v) for v in y],"certified_dual_lower":frac(lower),
                   "exact_one_graph_LP_optimum":lower==upper,"candidate_counterexample":upper<=actual_g-1}
        states[key]=out
        if upper<=actual_g-1:
            multiple=math.lcm(*(v.denominator for v in w))
            copies=[int(multiple*v) for v in w]
            assert sum(copies)<=multiple*(actual_g-1)
            assert all(sum(copies[j] for j,b in enumerate(a[i]) if b)>=multiple for i,c in enumerate(copies) if c)
            certificate={"cell":key,"base_adjacency":a,"girth":actual_g,"weights":[frac(v) for v in w],
                         "clone_multiple":multiple,"clone_counts":copies,"actual_binary_witness_vertices":sum(copies),
                         "minimum_outdegree_at_least":multiple,"legal_exact_blowup_certificate":True}
            print(json.dumps({"event":"EXACT_LEGAL_COUNTEREXAMPLE","cell":key,"utc":utc()}),flush=True);break
    if time.monotonic()-last>=45:
        print(json.dumps({"event":"progress","starts":starts,"cells":len(best),"elapsed_seconds":round(time.monotonic()-t0,3),
                          "minimum_observed_float_margin":min(v["discovery_margin_float"] for v in best.values())}),flush=True)
        last=time.monotonic()
result={"schema":"bounded-full-CH-negative-discovery-v1","started_utc":began,"finished_utc":utc(),
        "budget_seconds":SECONDS,"elapsed_seconds":time.monotonic()-t0,"seed":SEED,"starts":starts,
        "linear_program_failures":lp_failures,"full_target":"Every actual loopless binary digraph and every positive minimum-outdegree parameter.",
        "discovery_scope":"Only the listed actual saturated Hamiltonian base orders/girth thresholds, plus cycle-preserving mutations. This selected finite route does not prove the conjecture or a graph class.",
        "primary_equivalence":"St-Louis-Gendron-Hertz2009 Theorem6; exact rational cover yields a legal finite binary clone graph.",
        "acceptance":"Primal weights are rational, nonnegative and cover every active row exactly; total<=g-1 and exact base girth required. Float values alone are never accepted.",
        "cells":best,"legal_counterexample":certificate,"new_major_results":int(certificate is not None)}
path=Path(__file__).with_name("caccetta-haggkvist-fractional-cover-discovery.json")
path.write_text(json.dumps(result,indent=2)+"\n")
print(json.dumps({"event":"finished","path":str(path),"utc":result["finished_utc"],"starts":starts,
                  "elapsed_seconds":result["elapsed_seconds"],"exact_legal_counterexample":certificate is not None}),flush=True)
