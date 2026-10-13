"""Two bounded exact replica controls and a covariance-convexity countercheck.

All arithmetic used for certificates is integer/Fraction arithmetic.
This does not prove or refute complete Chollet. No Lean is run.
"""
from fractions import Fraction
from itertools import permutations
from pathlib import Path
import json

def zmul(z,w):
    return (z[0]*w[0]-z[1]*w[1],z[0]*w[1]+z[1]*w[0])
def zbar(z): return (z[0],-z[1])
def zadd(z,w): return (z[0]+w[0],z[1]+w[1])
def zscale(k,z): return (k*z[0],k*z[1])
def cycle_count(p):
    seen=set(); count=0
    for i in range(len(p)):
        if i not in seen:
            count+=1; j=i
            while j not in seen: seen.add(j); j=p[j]
    return count
def replica(a):
    n=len(a); terms={}
    for s in permutations(range(n)):
        v=(1,0)
        for i,j in enumerate(s): v=zmul(v,a[i][j])
        terms[s]=v
    coeff=[0]*(n+1)
    for s,fs in terms.items():
        inv=[0]*n
        for i,j in enumerate(s): inv[j]=i
        for t,ft in terms.items():
            k=cycle_count([inv[j] for j in t])
            product=zmul(fs,zbar(ft))
            coeff[k]+=product[0]
    p=sum(f[0] for f in terms.values())
    assert sum(f[1] for f in terms.values())==0
    assert sum(coeff)==p*p
    return {"coefficient_cycles_ascending":coeff,"permanent":p,
            "permanent_squared":p*p,
            "M2":str(sum(Fraction(coeff[k],2**(n-k)) for k in range(n+1))),
            "M2_over_M1":str(sum(Fraction(coeff[k],2**(n-k)) for k in range(n+1))/p**2),
            "formal_derivative_at_1":sum((k-n)*coeff[k] for k in range(n+1))}
def permanent(a):
    return sum((__import__("functools").reduce(lambda x,y:x*y,
                (a[i][j] for i,j in enumerate(s)),Fraction(1))
                for s in permutations(range(len(a)))),Fraction(0))
def main():
    y=[[(2 if i==j else -1,0) for j in range(3)] for i in range(3)]
    roots=[(1,0),(0,1),(-1,0),(0,-1)]
    tran=[[zadd((1,0),zscale(2,zmul(roots[i],zbar(roots[j]))))
           if i<4 and j<4 else (1,0) for j in range(5)] for i in range(5)]
    yr=replica(y); tr=replica(tran)
    assert yr["coefficient_cycles_ascending"]==[0,-6,72,78]
    assert tr["coefficient_cycles_ascending"]==[0,-15808,11760,110312,115248,32504]
    x=[[0,0,1,1],[0,0,-1,-1],[1,-1,0,0],[1,-1,0,0]]
    a=Fraction(3,4); eps=Fraction(1,16)
    c=[[Fraction(1) if i==j else a for j in range(4)] for i in range(4)]
    cp=[[c[i][j]+eps*x[i][j] for j in range(4)] for i in range(4)]
    cm=[[c[i][j]-eps*x[i][j] for j in range(4)] for i in range(4)]
    gap=permanent(c)-(permanent(cp)+permanent(cm))/2
    assert gap==Fraction(175,16384)
    out={"Y3_scaled_by_2":yr,"known_Tran_rank2_Gram_diagnostic":tr,
         "fixed_diagonal_covariance_Jensen_countercheck":{
             "off_diagonal":str(a),"epsilon":str(eps),
             "per_C":str(permanent(c)),"per_C_plus":str(permanent(cp)),
             "per_C_minus":str(permanent(cm)),"strict_Jensen_gap":str(gap),
             "actual_PSD_proof":"C has minimum eigenvalue1/4; norm X=2, so both perturbed matrices have minimum eigenvalue at least1/8."},
         "scope":"Exact checks of three route diagnostics only; no full Chollet statement or numerical search."}
    p=Path(__file__).with_name("chollet-replica-two-exact-controls.json")
    p.write_text(json.dumps(out,indent=2)+"\n")
    print(json.dumps(out,indent=2))
if __name__=="__main__": main()
