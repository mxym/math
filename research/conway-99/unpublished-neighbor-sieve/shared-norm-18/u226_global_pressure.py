"""The signed norm18 row converted to graph-wide compatible counts."""
from fractions import Fraction as Q
from higher_moments import rows

def check():
    rr=rows();keys=sorted(set().union(*rr));piv={}
    def reduce(v):
        for i,r in sorted(piv.items()):
            a=v[i];v=[x-a*y for x,y in zip(v,r)]
        return v
    for row in rr:
        v=reduce([Q(row.get(k,0)) for k in keys])
        if any(v):
            i=next(j for j,x in enumerate(v)if x);piv[i]=[x/v[i]for x in v]
    t={(0,0):-93,(0,14):-2,(0,16):5,(0,18):6,(0,20):1,(0,26):1,
       (1,21):17,(1,23):-2,(1,25):1,(1,27):1,(2,22):-5,(2,26):9,(2,28):-3,(3,37):-1}
    assert set(t)<=set(keys) and not any(reduce([Q(t.get(k,0))for k in keys]))
    # At most 6 wing components, at most (6-j)//2 long components.
    for j in range(7):
        assert 3*(2**(j+(6-j)//2))<=24+28*j
    assert 5544+28*851==29372
    assert 291*2402-9*4158-6*16166-17*29372==65240
    assert 291*344-9*4158==6*10447
    return True
if __name__=='__main__':assert check();print('Exact signed norm18 row; rank36 family floor 65240, rank38 oriented N18 floor 10447.')
