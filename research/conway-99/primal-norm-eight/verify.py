from itertools import combinations
from fractions import Fraction
shapes = {
    'bowtie': ((0,1),(1,2),(2,0),(0,3),(3,4),(4,0)),
    'house': ((0,1),(1,2),(2,3),(3,0),(0,4),(1,4)),
}
for name, edges in shapes.items():
    N = [set() for i in range(5)]
    for i,j in edges:
        N[i].add(j); N[j].add(i)
    D=[]
    for i,j in combinations(range(5),2):
        D.extend([(i,j)]*(2-int(j in N[i])-len(N[i]&N[j])))
    far = 99-5-(5*14-2*len(edges)-len(D))
    base = (4*far+sum(4+len(N[i])+len(N[j]) for i,j in D))//2
    assert (len(D),far,base) == ((4,40,96) if name=='bowtie' else (5,41,103))
    if name=='house':
        cut=(2,3)
        assert cut in D and all(set(cut)&set(p) for p in D)
    assert Fraction(base+2,3)+17 >= Fraction(base,2)
    print(name, D, far, base)
def bounds(P):
    g=P//6; d=5*P//2
    old=1398474+765072+18*P-48*d+2*(831600+36*P-2286*g)
    new=96*(2079-9*g)+103*(8316-6*P)
    return old,new,old+new
for i,x in enumerate((3156588,408390,3564978)):
    assert min(bounds(p)[i] for p in range(852)) == x
print('P=0',bounds(0),'P=851',bounds(851))
