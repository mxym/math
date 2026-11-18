"""Direct cube-cell/coordinate-fiber check, no graph-distance helper or third-party dependencies."""
from itertools import product

def need(p,msg):
    if not p: raise ArithmeticError(msg)
anchors=[tuple(21*((a*t)%682)//682 for a in (1,5,26,130)) for t in range(682)]
cells=set()
for z in anchors:
    for v in product(*(tuple((x+i)%21 for i in range(4)) for x in z)):
        if v in cells: raise ArithmeticError(('overlapping 4-cubes',z,v))
        cells.add(v)
need(len(cells)==682*4**4,'cell cardinality')
# Cubes of side two about (u,2u+z). These are disjoint for any fixed label,
# and the fiber/conflict quotient has exactly the seven neighboring labels.
e2=[(0,0),(0,1),(1,0),(1,1)]
supports=[]
for z in range(21):
    cellset=set()
    for u in range(21):
        for i,j in e2:
            point=((u+i)%21,(2*u+z+j)%21)
            need(point not in cellset,'overlap within fiber')
            cellset.add(point)
    need(len(cellset)==84,'fiber mass')
    supports.append(cellset)
for a,b in product(range(21),repeat=2):
    actual=not supports[a].isdisjoint(supports[b])
    expected=(a-b)%21 in {18,19,20,0,1,2,3}
    need(actual==expected,(a,b))
N=682*21**4
v=10359354480853559
need(v**8<N*(10**15)**8<(v+1)**8,'C21 integer rate bracket')
need(N==132636042 and N-11466**2==1166886,'size difference')
# Named predecessor (C19) averaged-expansion lower bound is smaller.
need(21*9357200030000797<19*v,'asymptotic check on BPZ C19 benchmark')
print(f'{len(anchors)} disjoint 4-cubes in the label torus; {len(cells)}/{21**4} cells; full product: {N} words.')
