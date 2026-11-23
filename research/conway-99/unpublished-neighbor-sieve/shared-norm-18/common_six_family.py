"""One all-rank six-family identity on the full common harmonic rows."""
from fractions import Fraction as Q
from higher_moments import rows

def check():
    rs=rows(); keys=sorted(set().union(*rs)); piv={}
    for r in rs:
        v=[Q(r.get(k,0)) for k in keys]
        for i,a in sorted(piv.items()):
            c=v[i];v=[x-c*y for x,y in zip(v,a)]
        if any(v):
            i=next(j for j,x in enumerate(v) if x);piv[i]=[x/v[i] for x in v]
    W={(0,0):82192,(0,14):8531,(0,16):34068,(1,25):4572,(2,28):8012,
       (2,34):132,(3,35):296,(4,46):631,
       (0,18):-20360,(0,20):-16532,(0,26):-888,(1,27):-444,
       (2,26):-6964,(2,30):-5016}
    S={(1,23):1,(0,0):-99,(0,14):-7}
    C339={(3,39):1,(0,0):-132,(2,22):-22,(1,23):-1,(0,14):7}
    assert set(W)|set(S)|set(C339)<=set(keys)
    z=[Q(W.get(k,0)+1200*S.get(k,0)+74*C339.get(k,0)) for k in keys]
    for i,a in sorted(piv.items()):
        c=z[i];z=[x-c*y for x,y in zip(z,a)]
    assert not any(z)
    print('Exact six-family identity in the common higher-moment row span.')
if __name__=='__main__':check()
