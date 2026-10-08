"""Exact integer tangent-rank checks. No floating-point rank decisions."""
import json
from pathlib import Path
import sympy as sp

E3 = [
[0,0,0,0,0,0],
[0,0,1,2,2,1],
[0,1,0,1,2,2],
[0,2,1,0,1,2],
[0,2,2,1,0,1],
[0,1,2,2,1,0],
]
# McNulty-Weigert appendix / Daniel McNulty thesis Appendix D.
E5 = [
[0,0,0,0,0,0,0,0,0,0],
[0,1,2,3,4,2,4,1,3,0],
[0,2,4,1,3,3,2,1,0,4],
[0,3,1,4,2,3,4,0,1,2],
[0,4,3,2,1,2,0,3,1,4],
[0,3,2,2,3,0,1,4,4,1],
[0,2,0,4,4,1,1,3,2,3],
[0,1,3,1,0,4,3,4,2,2],
[0,0,1,3,1,4,2,2,4,3],
[0,4,4,0,2,1,3,2,3,1],
]

def make_matrix(E,m):
    n=2*m
    assert len(E)==n and all(len(r)==n for r in E)
    assert all(x==0 for x in E[0]) and all(r[0]==0 for r in E)
    variables=[(a,j) for a in range(1,n) for j in range(1,n)]
    index={v:i for i,v in enumerate(variables)}
    rows=[]
    for a in range(n):
      for b in range(a+1,n):
        classes=[[j for j in range(n) if (E[a][j]-E[b][j])%m==r] for r in range(m)]
        assert all(len(c)==2 for c in classes), (a,b,classes)
        for r in range(1,m):
          vec=[0]*len(variables)
          for q,sgn in [(r,1),(0,-1)]:
            for j in classes[q]:
              for i,sgn2 in [(a,1),(b,-1)]:
                if (i,j) in index: vec[index[i,j]]+=sgn*sgn2
          rows.append(vec)
    return sp.Matrix(rows)

out=[]
for m,E in [(3,E3),(5,E5)]:
    L=make_matrix(E,m)
    _, pivots=L.T.rref()
    record={'m':m,'shape':L.shape,'rank':len(pivots),'dimension':L.cols,
            'pivot_rows':list(pivots)}
    if len(pivots)==L.cols:
        B=L[list(pivots),:]
        Binv=B.inv()
        assert B*Binv==sp.eye(L.cols)
        C=max(sum(abs(Binv[i,j]) for j in range(L.cols)) for i in range(L.cols))
        record.update(determinant=str(B.det()),inverse_infinity_norm=str(C),
                      exact_GH_counts_checked=True)
    out.append(record)
path=Path(__file__).with_name('tangent_rank_results.json')
path.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
