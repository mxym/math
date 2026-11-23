"""Finite arithmetic in the Hoffman bisection lemma (standard library)."""
from itertools import combinations
def cost(n,e):
    before=46+(21*n+2*n*n-14*e)+2*n
    return before+99-22*(4+n)
def main():
    # Hard upper edge caps on small induced sets under λ=1 and μ=2.
    for n,upper in ((4,4),(5,6),(6,9)):
        pairs=list(combinations(range(n),2));maximum=0;min8=6
        for mask in range(1<<len(pairs)):
            e=mask.bit_count()
            if e<=maximum and not(n==6 and e==8):continue
            N=[0]*n
            for i,(p,q) in enumerate(pairs):
                if mask>>i&1:N[p]|=1<<q;N[q]|=1<<p
            if all((N[p]&N[q]).bit_count()<=2-((N[p]>>q)&1) for p,q in pairs):
                maximum=max(maximum,e)
                if n==6 and e==8:min8=min(min8,min(v.bit_count()for v in N))
        assert maximum==upper
        if n==6:assert min8==2
    assert [cost(n,e)for n,e in ((6,8),(6,9),(7,10),(7,11),(8,12),(9,14))]==[23,9,22,8,25,32]
    # D has 84 vertices, five all-D triangles per vertex; each Xi has size 21.
    for ell in range(15):
        d=84-ell;b=c=105-d;a=140-b-c-d
        assert a==14-ell
    print("small graph caps, shore transfers, and triangle arithmetic verified")
if __name__=="__main__":main()
