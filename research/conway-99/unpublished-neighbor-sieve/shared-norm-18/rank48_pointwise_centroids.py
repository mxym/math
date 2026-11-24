"""Two exact pointwise identities by three rank-48 quadratic projections."""
from collections import Counter
from higher_moments import SHIFTS, projections, dot

def row(shift, h):
    z=Counter()
    for j,m in [(1,48),(2,1)]:
        for (a,t),ws in projections(shift,j).items():
            if a:
                z[100*a+t]+=m*sum(dot(w,h) for w in ws)
    return {k:v for k,v in z.items() if v}
a=SHIFTS[1]; b=SHIFTS[2]
R1=row(b,(0,0,0,1))
r1={121:-3,123:1,125:1,127:-1,226:4,228:-2,230:-1,333:-1,335:1,337:-1,444:-1}
assert R1=={k:3*v for k,v in r1.items()}
R2=Counter({k:18*v for k,v in r1.items()})
R2.subtract(row(a,(0,1,1,0)))
R2.subtract({k:2*v for k,v in row(b,(0,1,1,0)).items()})
r2={121:-32,123:7,125:6,127:-8,129:1,222:-7,226:38,228:-19,230:-6,335:9,337:-9,444:-9}
assert {k:v for k,v in R2.items() if v}==r2
print('two conditional-free determinant-49 centroid rows verified.')

# Optional site check of the 1732 baseline in the worked example.
def baseline():
    from original_site_populations import calc
    from rank36_three_types import UNIT
    import sympy as sm
    one,w,c,g,u,ub,red=calc(42,[],export=True)
    A=[red(u[k]) for k in sorted(UNIT-{(0,26),(2,28),(2,30)})]
    A.extend(red(w(k)) for k in [(0,14),(2,22),(3,35),(4,44)])
    A.append(red(w((1,23))-99*one))
    K=sm.Matrix.hstack(*sm.Matrix(A).nullspace())
    assert not any(sm.Matrix([red(g((2,30))-1732*one)])*K)
if __name__=='__main__':baseline()
