"""Separate the neutral norm-28 population in each maximal extension."""
from fractions import Fraction as Q
from higher_moments import rows

def main():
    rs=rows();keys=sorted(set().union(*rs));piv={}
    for r in rs:
        v=[Q(r.get(k,0)) for k in keys]
        for i,a in sorted(piv.items()):
            c=v[i];v=[x-c*y for x,y in zip(v,a)]
        if any(v):
            i=next(j for j,x in enumerate(v) if x);piv[i]=[x/v[i] for x in v]
    rhs={(0,0):238,(0,14):10,(0,16):72,(0,18):40,(0,20):16,(0,22):8,
         (1,21):32,(2,22):8,(2,26):32,(2,28):8,(3,33):16,(3,35):8,(4,44):8}
    # Add 6S, and move Z=W028 to the same side.
    for k,c in {(1,23):6,(0,0):-594,(0,14):-42,(0,28):-1}.items():
        rhs[k]=rhs.get(k,0)+c
    assert set(rhs)<=set(keys)
    z=[Q(rhs.get(k,0)) for k in keys]
    for i,a in sorted(piv.items()):
        c=z[i];z=[x-c*y for x,y in zip(z,a)]
    assert not any(z)
    print('Neutral W028 identity verified; every extension has Z >= 238+5 N18(H).')
if __name__=='__main__':main()
