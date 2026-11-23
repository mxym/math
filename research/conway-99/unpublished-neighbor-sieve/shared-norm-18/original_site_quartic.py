"""Replay the original rank-44 graph-site harmonic quartic identities, with no solver."""
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import runpy

def basis():
    form = runpy.run_path(str(Path(__file__).resolve().parents[2] /
                              "maximal-marked-lattice" / "verify.py"))["form"]
    def conv(f,g):
        return [sum(f[i]*g[n-i] for i in range(n+1)) for n in range(17)]
    b = {}
    for a,l,r in product(range(3,14,2),(False,True),(False,True)):
        h=26-a
        x=list(map(Q,conv(form(a,l),form(h,r))))
        power=(2*l-1)*((a-1)//2)+(2*r-1)*((h-1)//2)
        y=[Q(7)**power*u for u in conv(form(a,not l),form(h,not r))]
        for i in range(17):
            t=x[i]
            if not t: continue
            if i not in b:
                b[i]=([u/t for u in x],[u/t for u in y])
                break
            f,g=b[i]
            x=[v-t*u for v,u in zip(x,f)]
            y=[v-t*u for v,u in zip(y,g)]
    assert set(b)==set(range(17))
    return b

def identities():
    b=basis()
    for rank in (36,38,40,42):
        h=7**((rank-36)//2)
        scale=7**(rank//2-11+2)   # graph-scale Z, including 7^(degree/2)
        directions=[b[i] for i in range(7,17)]  # X0 through X6 zero
        for A,B in [
            ([574,252,105,40,14,4,1],[1034,44,1,0]),
            ([97776,25494,5208,556,-168,-111,-40],[-28240,-900,0,1])
        ]:
            residual=[h*sum(u*v for u,v in zip(A,x[7:14]))
                      -7*scale*sum(u*v for u,v in zip(B,y[1:5]))
                      for x,y in directions]
            constants=[y[0] for x,y in directions]  # transformed cusp constant 0
            j=next(j for j,c in enumerate(constants) if c)
            assert all(e*constants[j]==residual[j]*c for e,c in zip(residual,constants))
        print("rank",rank,": both original quartic identities passed")

def low_mark_values():
    q0=lambda t: 69*t-2*t*t
    q3=lambda t:115*t-3289-2*(t-11)**2
    excess=lambda x:69*(x**4-x*x)+92*(x**3-x)
    assert [q0(t) for t in range(14,27,2)]==[574,592,594,580,550,504,442]
    assert [q3(t) for t in (33,35,37,39,53)]==[-462,-416,-386,-372,-722]
    assert (q0(28)-q3(39),q0(42)-q3(53))==(736,92)
    assert (excess(2),excess(-2))==(1380,276)
    assert 2*22*excess(2)==60720
    neutral_surplus=92+2*69*(3**4-3**2)
    path_surplus=2*excess(2)+3*excess(-2)
    assert (neutral_surplus,path_surplus)==(10028,3588)
    # No use of vertex relabelings as graph automorphisms.
    six_floor=min(sum(excess(i-4) for i in ds) for ds in product(range(6),repeat=6) if sum(ds)==16)
    assert six_floor==552
    six_marks=20790-9*851-36*(851//6)
    assert six_marks==8055
    gamma0=8316*(neutral_surplus+2*path_surplus)
    gamma=gamma0+2*six_marks*six_floor
    assert (gamma0,gamma)==(143068464,151961184)
    print("graph mark surpluses:",60720,gamma0,gamma)

if __name__=="__main__":
    identities()
    low_mark_values()
