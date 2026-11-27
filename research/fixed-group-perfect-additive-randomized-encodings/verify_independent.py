#!/usr/bin/env python3
"""Independent truth-table and direct convolution checks."""
from itertools import combinations, product

def classification(shape):
    points=list(product(*(range(x) for x in shape)))
    indices=dict(zip(points,range(len(points))))
    anch=(0,)*len(shape)
    axes=[[indices[anch[:i]+(a,)+anch[i+1:]] for a in range(x)]
          for i,x in enumerate(shape)]
    boxes=[]
    per_axis=[[] for _ in shape]
    for i,j in combinations(range(len(shape)),2):
        for x in points:
            for y in points:
                if i==j or x[i]>=y[i] or x[j]>=y[j]: continue
                if any(x[q]!=y[q] for q in range(len(shape)) if q not in (i,j)): continue
                a=x[:i]+(y[i],)+x[i+1:]
                b=x[:j]+(y[j],)+x[j+1:]
                boxes.append(tuple(indices[z] for z in (x,y,a,b)))
    for i in range(len(shape)):
        for x in points:
            for t in range(x[i]+1,shape[i]):
                y=x[:i]+(t,)+x[i+1:]
                per_axis[i].append((indices[x],indices[y]))
    exact_even=exact_odd=0
    for mask in range(1<<len(points)):
        vals=[(mask>>i)&1 for i in range(len(points))]
        rect=all(sum(vals[i] for i in box)%2==0 for box in boxes)
        loc=[[vals[t]^vals[0] for t in axis] for axis in axes]
        pred=[(vals[0]+sum(loc[i][t] for i,t in enumerate(x)))%2 for x in points]
        assert rect==(pred==vals)
        essential=sum(any(vals[a]!=vals[b] for a,b in e) for e in per_axis)
        if rect:
            assert essential==sum(any(a) for a in loc)
            assert [int((vals[0]+sum((3*loc[i][t]) for i,t in enumerate(x))//3)%2)
                    for x in points]==vals
            exact_even+=1
        if essential<=1:
            assert rect
            exact_odd+=1
    assert exact_even==1<<(1+sum(q-1 for q in shape))
    assert exact_odd==2+sum((1<<q)-2 for q in shape)
    return 1<<len(points)

truth=sum(classification(s) for s in [(2,2),(2,3),(2,2,2),(1,3,2),(2,2,3)])
print(f"mixed rectangles and fixed-group Boolean classes: {truth} tables")

def compositions(total,n):
    if n==1:
        yield (total,)
    else:
        for j in range(total+1):
            for tail in compositions(total-j,n-1): yield (j,)+tail

def conv(a,b,add):
    z=[0]*len(a)
    for i in range(len(a)):
        for j in range(len(b)):
            z[add[i][j]]+=a[i]*b[j]
    return tuple(z)

def group(shape):
    gs=list(product(*(range(q) for q in shape)))
    ix={a:i for i,a in enumerate(gs)}
    return [[ix[tuple((x+y)%q for x,y,q in zip(a,b,shape))] for b in gs] for a in gs]

comparisons=collisions=disjoint_collisions=0
for shape in [(2,),(3,),(4,),(5,),(2,2),(3,3)]:
    add=group(shape)
    for mass in range(1,5):
        laws=list(compositions(mass,len(add)))
        square=[conv(x,x,add) for x in laws]
        support=[sum(1<<i for i,z in enumerate(x) if z) for x in laws]
        this_disjoint=0
        for j in range(len(laws)):
            for i in range(j):
                comparisons+=1
                if square[i]!=square[j]: continue
                collisions+=1
                if not support[i]&support[j]:
                    this_disjoint+=1
        if len(add)%2: assert this_disjoint==0
        else: assert this_disjoint>0
        disjoint_collisions+=this_disjoint

# In odd order, agreement of squares alone does not identify the law.
z3=group((3,))
assert conv((3,1,2),(3,1,2),z3)==conv((1,3,2),(1,3,2),z3)
# In even order, disjointness does not help without the odd-order condition.
z4=group((4,))
assert conv((1,0,0,0),(1,0,0,0),z4)==conv((0,0,1,0),(0,0,1,0),z4)
# Explicit perfect XOR over C4.
assert [z4[a][b] for a,b in product([0,2],repeat=2)]==[0,2,2,0]
print(f"direct square convolutions: {comparisons} pairs; {collisions} equal squares; {disjoint_collisions} disjoint even-order examples")
print("overlapping odd-order equality and disjoint even-order equality negative controls PASS")
print("verify_independent: PASS")
