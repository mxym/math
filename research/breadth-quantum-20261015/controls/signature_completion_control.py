"""Exact adversarial checks for the fixed-H rank-two completion argument.
This is a two-copy restricted explanation within already-known results.
"""
from pathlib import Path
import argparse,itertools,json,datetime
import sympy as sp
ap=argparse.ArgumentParser();ap.add_argument('--output',required=True);args=ap.parse_args();p=Path(args.output).resolve();assert not p.exists()
l=sp.Symbol('lambda',real=True);eye=sp.eye(2);H4=sp.diag(1,1,-1,-1);support=[3,6,1,2]
def embed(M):
    N=sp.zeros(9)
    for i,j in itertools.product(range(4),repeat=2):N[support[i],support[j]]=M[i,j]
    return N
def partial(M,j):return sp.Matrix(3,3,lambda a,b:sum(M[3*t+a,3*t+b] if j==0 else M[3*a+t,3*b+t] for t in range(3)))
def q(M):return sp.expand((M.H*M).trace()-l*sum((partial(M,j).H*partial(M,j)).trace() for j in [0,1])+l*l*sp.conjugate(M.trace())*M.trace())
rotation=sp.Matrix([[sp.Rational(3,5),sp.Rational(4,5)],[-sp.Rational(4,5),sp.Rational(3,5)]])
rows=[]
for E,A,U in [(sp.zeros(2),eye,eye),(sp.diag(sp.Rational(3,4),sp.Rational(4,3)),sp.diag(sp.Rational(5,4),sp.Rational(5,3)),rotation),(sp.Matrix([[0,3*sp.I/4],[-3*sp.I/4,0]]),5*eye/4,sp.diag(1,sp.I))]:
    assert U.H*U==eye and A*A==eye+E*E and E.H==E
    F=A*U;G=U.H*E*U;K4=E.row_join(F).col_join(F.H.row_join(G));K=embed(K4);H=embed(H4)
    assert K4*H4*K4==-H4 and (H+sp.I*K).rank()==2
    s=sp.simplify((E*E).trace());t=sp.simplify(E.trace())
    formula=4+(4-2*l)*s+(4*l*l-2*l)*t*t
    assert sp.simplify(q(K)-formula)==0 and sp.simplify(q(H+sp.I*K)-(q(H)+q(K)))==0
    rows.append({'E':str(E),'unitary_U':str(U),'trace_E2':str(s),'trace_E':str(t),'actual_completion_rank':2,'exact_QK':str(sp.factor(formula))})
assert sp.expand(4-6*l+8*l*l-(8*(l-sp.Rational(3,8))**2+sp.Rational(23,8)))==0
out={'schema':'exact-fixed-H-completion-controls-v1','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'scope':'Checks illustrate the written all-completion argument for one fixed H. This lies within known two-copy Werner undistillability, and is not a full N0 solution or new major result.','rows':rows,'all_completion_written_bound':'Q_2(K)>=4+(4-6lambda+8lambda^2)Tr(E^2)>=4 for0<=lambda<=1/2','minimum_QH_plus_QK':'8-12lambda>=2','complete_target_solved':False,'new_major_results':0}
p.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'output':str(p),'exact_checks_passed':len(rows),'complete_target_solved':False}))
