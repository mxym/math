"""Rank-independent oriented N18 population identity; run beside higher_moments.py."""
from fractions import Fraction as Q
from higher_moments import rows

def verify():
    E=rows()
    # Full standardized target: 48V018 + ... - 70W014 - 7S - 1680 = 0.
    # S=W123-99W000-7W014.
    target={(0,0):-987,(0,14):-21,(0,16):-2,(0,18):48,(0,20):-3,(0,26):3,
            (1,21):51,(1,23):-7,(1,25):2,(1,27):4,(2,28):1,(2,30):2,
            (3,33):-12,(3,35):-6,(3,37):3,(4,44):-8}
    keys=sorted(set().union(*E))
    assert set(target)<=set(keys)
    basis={}
    def reduce(d):
        v=[Q(d.get(k,0)) for k in keys]
        for i,r in sorted(basis.items()):
            c=v[i]
            if c:v=[x-c*y for x,y in zip(v,r)]
        return v
    for d in E:
        v=reduce(d)
        if any(v):
            j=next(i for i,c in enumerate(v) if c)
            basis[j]=[c/v[j] for c in v]
    assert not any(reduce(target))
    print("Full unit-coordinate N18 identity checked. Sparse lower bound 35p:",[35*p for p in (344,50,8)])
if __name__=='__main__':verify()
