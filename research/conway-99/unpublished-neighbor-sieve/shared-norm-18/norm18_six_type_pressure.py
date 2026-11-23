from fractions import Fraction as Q
from higher_moments import rows

def verify():
    E=rows()
    forbidden={(0,16),(0,20),(0,26),(1,21),(1,27),(2,30)}
    # 4W022 - 12V018 + 420 + 14W014 + 2W335 + S = 0,
    # Restricted to six absent selected UNIT coordinates; all three newly allowed counts remain.
    target={(0,0):321,(0,14):7,(0,18):-12,(0,22):4,(1,23):1,(3,35):2,(1,25):-2,(2,28):5,(3,37):-1}
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
    assert 21*(2058*344-12*4158)-44*267960==2028936
    assert 84*16166<2028936
    print("rank 38 six-type face: 84N18 +200U125 -1004U228 +58U337 >= 2028936")
if __name__=='__main__':verify()
