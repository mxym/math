"""Delete Fano-positive tuples and recompute the three-coclique overlap bounds."""
from itertools import combinations_with_replacement

def affine_dim(n):
    return 0 if n == 0 else (24*(n-1)+n+23)//(n+24)

def independent_cap(m, dimension):
    return max(sum(v) for v in combinations_with_replacement(range(m+1),4)
               if sum(map(affine_dim,v))+2*(v[1]>0)<=dimension)

def main():
    tuples=[]
    for m in (1,3):
        for s in range(190//9+1):
            w34=189-42*m-9*s
            w18,rem=divmod(291+5*m+2*s,6)
            if w34>=0 and rem==0:
                tuples.append((m,s,w18,w34))
    assert tuples == [(1,2,50,129),(1,5,51,102),(1,8,52,75),(1,11,53,48),
                      (1,14,54,21),(3,0,51,63),(3,3,52,36),(3,6,53,9)]
    assert max(b for m,a,b,d in tuples)==54
    for m,expect in [(51,45),(52,47),(53,49)]:
        cap=independent_cap(m,41)
        assert cap==114 and (4*m-cap+1)//2==expect
    print("Eight Fano-free tuples; M=3 matching bounds 45, 47, 49 verified.")

if __name__=="__main__":
    main()
