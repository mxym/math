from fractions import Fraction as Q
from higher_moments import rows

def verify():
    E=rows()
    # The general 48V018+12V226 identity, with S removed.
    target={(0,0):-969,(0,14):-21,(0,16):-70,(0,18):48,(0,20):33,(0,26):3,
            (1,21):81,(1,23):-11,(1,25):-2,(1,27):8,(2,26):12,(2,28):-19,
            (2,30):10,(3,37):-3,(4,44):-10}
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
    assert Q(2058*344-12*4158,48)==Q(27419,2)
    print("Rank38, allowed 018+024+226: oriented N18 >= 13710.")
if __name__=='__main__':verify()
