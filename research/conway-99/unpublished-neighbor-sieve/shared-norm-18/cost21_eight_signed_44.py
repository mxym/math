"""Odd signed classes on the last cost-21 profile. Requires SymPy; run next to rank42_u121_residues.py."""
from rank42_u121_residues import shifts,pts,group,pairs,anti,dot,B
from collections import Counter
import sympy as sm

# The published projective even chart includes nine raw species (two transfers).
# In addition, fixed G121 on opposite classes, G127=9 signed N18 and G335=0
# give zero skew in those three species for the *individual profile*.
tables={s:list(pts(s))for s in shifts};rs=[]
for o in group:
 for s,points in tables.items():
  for i,j in pairs:
   r=Counter()
   for a,n,g,c,m in points:
    if c==(0,0) or not a or (a,n) in ((1,21),(1,27),(3,35)):continue
    b=tuple(dot(z,c)%7 for z in o); rep=anti(b)
    r[(a,n),rep]+=m*(1 if b==rep else -1)*(2*g[i]*g[j]-B[i][j]*g[0]**2)
   rs.append({k:z for k,z in r.items()if z})
K=sorted(set().union(*rs))
assert sorted(set(k[0]for k in K))==[(1,25),(1,29),(2,32),(3,33),(4,44)]
rank=sm.Matrix([[r.get(k,0)for k in K]for r in rs]).to_DM().rank()
assert len(K)==rank==20
print('positive-charge opposite-residue differences all zero on 125,129,232,333,444; one true 44-set per signed residue.')

# In the sole remaining tuple the raw 335 mass must vanish, independently of y.
def check_native_335():
    from original_site_populations import calc
    from rank36_three_types import UNIT
    o,w,c,g,u,ub,red=calc(42,[],export=True)
    face=[red(u[k]) for k in sorted(UNIT-{(0,18),(1,21),(1,25)})]
    face.extend(red(v) for k,v in ub.items() if str(k).startswith('compat'))
    r=w((1,21)); f=w((0,14))*sm.Rational(1,2); M=w((2,22))
    S=w((1,23))-99*o-14*f; Q=g((4,44))
    rel=3*g((3,35))+3168*o+172*r+256*f-184*M+12*S+10*Q
    K=sm.Matrix.hstack(*sm.Matrix(face).nullspace())
    assert not any(sm.Matrix([red(rel)])*K)
    assert -3168-172*10+184*27-10*8 == 0
    print('205-variable exact mass relation: G335=0 in the sole aggregate.')

if __name__=='__main__': check_native_335()
