from original_site_populations import calc
from rank36_three_types import UNIT
import sympy as sm
o,w,c,g,u,ub,red=calc(42,[],export=True)
A=sm.Matrix([red(u[k])for k in sorted(UNIT-{(0,26),(2,28),(2,30)})]);H=sm.Matrix.hstack(*A.nullspace())
def qq(k):return g(divmod(k,100))
B=w((0,14));S=w((1,23))-99*o-7*B;M=w((2,22));h=qq(335)+qq(444)
rels=[
 2*qq(333)-808*o-16*(M+S)-96*B-h,
 qq(228)-784*o-8*S-56*B-h,
 qq(26)-4680*o-40*(M+S)-296*B-3*h]
for z in rels:assert not any(sm.Matrix([red(z)])*H)
print('three raw graph-mass identities verified; G333>=404, G228>=784, N26>=4680.')
