"""Exact PG(2,3) and complementary configuration permanent baselines.

Subset matching DP and inclusion-exclusion are independently structured.
No new Ryser theorem, counterexample, Lean audit or search-exhaustion claim.
"""
from itertools import product
from pathlib import Path
import json
def projective_vectors():
    out=[]
    for v in product(range(3),repeat=3):
        if v==(0,0,0): continue
        lead=next(x for x in v if x)
        inv=1 if lead==1 else 2
        w=tuple(inv*x%3 for x in v)
        if w not in out: out.append(w)
    return sorted(out)
def matching_dp(rows,n):
    d=[0]*(1<<n); d[0]=1
    for mask in range(1<<n):
        i=mask.bit_count()
        if i==n: continue
        bits=rows[i]&~mask
        while bits:
            bit=bits&-bits; bits-=bit
            d[mask|bit]+=d[mask]
    return d[-1]
def ryser(rows,n):
    total=0
    for mask in range(1<<n):
        v=1
        for row in rows: v*=(row&mask).bit_count()
        total+=(-1 if (n-mask.bit_count())%2 else 1)*v
    return total
def main():
    points=projective_vectors(); n=len(points); assert n==13
    rows=[sum(1<<j for j,p in enumerate(points)
              if sum(a*b for a,b in zip(line,p))%3==0) for line in points]
    comp=[((1<<n)-1)^r for r in rows]
    def record(rows,k,expected):
        assert all(r.bit_count()==k for r in rows)
        assert all(sum(bool(r&(1<<j)) for r in rows)==k for j in range(n))
        p=matching_dp(rows,n); q=ryser(rows,n); assert p==q==expected
        lam=k*(k-1)//(n-1)
        assert all((rows[i]&rows[j]).bit_count()==lam
                   for i in range(n) for j in range(i))
        return {"n":n,"row_and_column_sum":k,"lambda":lam,
                "rows_as_bitmasks":rows,
                "binary_matrix":[[int(bool(r&(1<<j))) for j in range(n)] for r in rows],
                "permanent_matching_dp":p,"permanent_ryser":q}
    out={"date":"2026-10-14","points_and_lines_GF3":points,
         "configuration":record(rows,4,3852),
         "complement":record(comp,9,64803969),
         "scope":"Exact baseline only; not a new positive Ryser result or a counterexample."}
    p=Path(__file__).with_name("ryser-pg23-baseline.json")
    p.write_text(json.dumps(out,indent=2)+"\n")
    print({k:{j:v for j,v in x.items() if j not in["binary_matrix"]}
           for k,x in out.items() if isinstance(x,dict)})
if __name__=="__main__": main()
