"""Exact finite certificates for the concrete comparisons. Standard library only."""
from fractions import Fraction as F
from itertools import product
q=7
reps=[(1,i,j) for i,j in product(range(q),repeat=2)]+[(0,1,j) for j in range(q)]+[(0,0,1)]
rows=[sum(1<<j for j,y in enumerate(reps) if sum(a*b for a,b in zip(x,y))%q==0) for x in reps]
assert len(rows)==57 and len(set(rows))==57
assert all(row.bit_count()==8 for row in rows)
assert all(sum((row>>i)&1 for row in rows)==8 for i in range(57))
assert all((x&y).bit_count()==(8 if i==j else 1) for i,x in enumerate(rows) for j,y in enumerate(rows))
assert F(7,64)>F(5,49)
assert all(pow(7,6*m+1,36)==7 for m in range(1000))
print('PG(2,7): 57 points, 57 lines, 456 flags, all 3249 Gram entries agree with 7I+J.')
print('Squared gaps: 7/64 > 5/49; integer comparison 343 > 320.')
for a,b,expected in [(20,50,F(60,7)),(50,150,F(25)),(30,150,F(20))]:
    mu=F(2*a*b,a+b)
    g=min(abs(mu-x) for x in (0,a,b,a+b))
    assert g==expected and g>7
    print(f'K_({a},{b}): min={a}, max={b}, mean={mu}, unnormalized central gap={g} > 7.')
