"""Exact finite reduction for the 36-site unit double. Python standard library only."""
from itertools import combinations, combinations_with_replacement, permutations, product
from math import comb

P=list(permutations(range(4),2))
A=[[int(i==k)-int(j==k) for k in range(4)] for i,j in P]
M={(0,1):4,(2,3):4,(0,2):7,(0,3):7,(1,2):7,(1,3):7}
DEAD={13:[(0, 37), (1, -213), (2, 4), (3, 4), (4, -1473), (5, 4), (6, -2051), (7, 4), (8, -2644), (9, 4), (10, 4), (11, -1664), (12, 4), (28, 154), (44, -327), (64, -214), (69, -56), (77, 38), (79, -15), (84, 38), (87, -38), (92, -36), (93, -57), (96, 61), (100, 74), (103, -18), (107, -251), (110, -354), (111, 354), (113, 368), (114, 75), (115, 20), (116, 158), (118, -137), (119, -57), (120, 82), (121, -38), (122, -20), (123, 404), (124, 18), (126, -61), (127, 36), (130, -38), (134, -211), (137, -253), (138, 179), (139, -101), (140, 267), (141, -13), (142, 150), (143, 312), (144, -162), (145, 20), (146, -56), (148, 18), (150, 253), (151, -217), (152, 101), (153, -267), (155, 354), (156, -280), (158, -368), (159, 18), (161, 392), (162, 38), (165, -88), (166, 97), (167, 122), (168, 69)],
17:[(0, 2), (1, 2), (2, 2), (3, 2), (4, 2), (5, 2), (6, 2), (7, 2), (8, 2), (9, 2), (10, 2), (11, 2), (12, 9), (17, 20), (21, 5), (24, 4), (26, -5), (31, -16), (42, -42), (45, -8), (49, 15), (54, 6), (57, -37), (62, -7), (68, -9), (75, -3), (79, -10), (84, 5), (90, 6), (93, 11), (94, 3), (96, -6), (97, 7), (100, -2), (101, 10), (103, -16), (105, -7), (107, -36), (108, -10), (109, 28), (110, -11), (111, 30), (114, -25), (115, 6), (116, 21), (118, -22), (120, 11), (121, -15), (122, -22), (125, 11), (127, 9), (129, 6), (131, 7), (133, -20), (135, -21), (136, -14), (137, 4), (139, -24), (140, 10), (141, -17), (143, 31), (145, 29), (146, -7), (147, -9), (148, -2), (150, 13), (152, 43), (153, 11), (154, -12), (156, -13), (158, -2), (161, 11), (162, 4), (163, -13), (166, -2), (167, 8)]}
def decks():
    maps=[]
    for g in permutations(range(4)):
        if all(M[tuple(sorted((g[i],g[j])))]==m for (i,j),m in M.items()):
            for swap in range(2):
                maps.append([P.index((g[j],g[i]) if swap else (g[i],g[j])) for i,j in P])
    D=[]
    for v in product(*(range(m+1) for m in M.values())):
        d=[0]*12
        for ((i,j),m),w in zip(M.items(),v):
            d[P.index((i,j))]=w
            d[P.index((j,i))]=m-w
        if any(sum(h*a[k] for h,a in zip(d,A)) for k in range(4)):continue
        if all(d<=[d[k] for k in sigma] for sigma in maps):D.append(tuple(d))
    return D

def options(v):
    sig=A[v] if v<12 else [0]*4
    # Tail/head degree maxima. At an active site all four neighbors of the
    # opposite sign are needed. At an inactive site the height is at most 3.
    tgt=[4 if x==-1 else 0 if x==1 else 3 for x in sig]
    head=[4 if x==1 else 0 if x==-1 else 3 for x in sig]
    out=[0]*4; inc=[0]*4; w=[0]*12
    def go(k):
        if k==12:
            if all(out[i]-inc[i]==-4*sig[i] for i in range(4)):yield tuple(w)
            return
        i,j=P[k]
        for n in range(1+min(tgt[i]-out[i],head[j]-inc[j])):
            out[i]+=n;inc[j]+=n;w[k]=n
            if k%3!=2 or not sig[i] or out[i]==tgt[i]:yield from go(k+1)
            out[i]-=n;inc[j]-=n
    yield from go(0)

def admissible(d,v,h):
    if not d[v] or any(i>j for i,j in zip(h,d)):return False
    for other in (2,3):
        cut=[a[0]+a[other] for a in A]
        x=cut[v] if v<12 else 0
        if x and any(j and cut[k]==x for k,j in enumerate(h)):return False
        if not x and sum(k for k,g in zip(h,cut) if g==1)>4:return False
    for g,a in enumerate(d[:12]):
        if a!=5:continue
        i,j=P[g]
        z=3 if v<12 and P[v]==(j,i) else 2 if v<12 and (P[v][0]==j or P[v][1]==i) else -1
        if (h[g]!=z if z>=0 else h[g]>1):return False
    return True

def minimum(s,b):
    q,r=divmod(s,b)
    return (b-r)*comb(q,2)+r*comb(q+1,2)

def occupancy_possible(a,b):
    # Reverse counts need only be tried for the large class a>=4 (b<=3).
    # Each pair of reverse sites has at most two common neighbors in A.
    if a<4:return True
    for rev in product(range(5),repeat=b):
        if any(x+y>a+2 for x,y in combinations(rev,2)):continue
        n=4*a-sum(rev)
        if n<0 or n>4*(9-b):continue
        if sum(comb(h,2) for h in rev)+2*minimum(n,9-b)<=2*comb(a,2):return True
    return False

def rows(v,h):
    h=h+(14-sum(h),)
    assert min(h)>=0
    yield from (int(i==v) for i in range(13))
    for i,j in combinations(range(13),2):
        yield int(i==v)*h[j]-int(j==v)*h[i]
    for i,j in combinations_with_replacement(range(12),2):
        yield h[i]*(h[j]-int(i==j))+int(i==v)*h[j]

def rhs(d):
    yield from d
    yield from (0 for _ in combinations(range(13),2))
    for i,j in combinations_with_replacement(range(12),2):
        yield 2*d[i]*(d[j]-int(i==j))

def score(cert,x):
    return sum(c*e for c,e in zip(cert,x,strict=True))

def main():
    D=decks();assert len(D)==19
    rem=[i for i,d in enumerate(D) if all(occupancy_possible(a,d[P.index((j,i))]) for (i,j),a in zip(P,d))]
    assert rem==[10,13,14,17,18],rem
    O=[list(options(v)) for v in range(13)]
    assert [len(x) for x in O]==[65]*12+[2008]
    for k in (13,17):
        cert=[0]*169
        for j,w in DEAD[k]:cert[j]=w
        d=D[k]+(63,)
        values=[score(cert,rows(v,h)) for v in range(13) for h in O[v] if admissible(d,v,h)]
        z=score(cert,rhs(d))
        assert len(values)=={13:953,17:752}[k]
        assert min(values)>=0 and z=={13:-594,17:-783}[k]
        print("deck",k,"columns",len(values),"minimum",min(values),"negative RHS",z)
    print("remaining formal directed mass decks:")
    for k in (10,14,18):print(k,D[k])
if __name__=='__main__':main()
