from fractions import Fraction as Q
from higher_moments import rows

def verify():
    E=rows()
    forbidden={(0,16),(0,20),(0,26),(1,21),(1,25),(1,27),(2,28),(2,30),(3,37)}
    # 4W022 - 12V018 + 420 + 14W014 + 2W335 + S = 0,
    # after S = W123 - 99 - 7W014. Only restrict the 9 absent UNIT coordinates.
    target={(0,0):321,(0,14):7,(0,18):-12,(0,22):4,(1,23):1,(3,35):2}
    keys=sorted(set().union(*E)-forbidden)
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
    assert 3*16166-105*344==12378
    assert 6*(9*13772-110880)>15*(3*13772-36120)
    print("N22 <= 3*N18-36120 <= 12378 at rank 38 on 018,024,226.")
if __name__=='__main__':verify()
