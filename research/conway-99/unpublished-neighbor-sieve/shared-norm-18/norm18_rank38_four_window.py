"""Rank38 four-type window. All graph counts are literal and not class averages."""
from fractions import Fraction as Q
from rank38_three_hit_sets import engine
from rank36_three_types import UNIT


def check():
    R, C, D, one = engine()
    def lin(*terms):
        return [sum(c*r[i] for c,r in terms) for i in range(len(one))]
    def w(a,t):return R['w',(a,t)]
    p = 344
    mantel = lin((110880,one),(-9*p,D[0,18]))
    # All rows after the first two terms in each row equality are nonnegative.
    # We reduce modulo the exactly eight absent selected types below.
    data = [
        ((0,18), Q(57878,5),1,[w(0,14),w(2,22),w(3,33),w(3,35),w(4,44),R['S']],
          [Q(7052,15),Q(172,15),Q(516,5),Q(258,5),Q(258,5),Q(688,15)]),
        ((2,26), Q(8728,3),1,[w(0,14),w(2,22),R['S'],mantel],
          [Q(5504,9),Q(1720,9),Q(688,9),Q(2,27)]),
        ((2,30),Q(39392,3),-1,[w(0,14),w(2,22),w(3,33),w(3,35),R['S'],mantel],
          [Q(4472,9),Q(2752,9),688,344,Q(172,9),Q(8,27)])]
    piv={}
    skip=sorted(UNIT-{(0,18),(0,24),(2,26),(2,30)})
    assert len(skip)==8
    for k in skip:
        v=list(D[k])
        for i,r in sorted(piv.items()):
            c=v[i];v=[a-c*b for a,b in zip(v,r)]
        if any(v):
            i=next(i for i,x in enumerate(v) if x);piv[i]=[x/v[i] for x in v]
    for k,B,s,rows,coeffs in data:
        assert all(x>0 for x in coeffs)
        v=lin((s*p,D[k]),(-s*B,one),*((-c,r) for c,r in zip(coeffs,rows)))
        for i,r in sorted(piv.items()):
            c=v[i];v=[a-c*b for a,b in zip(v,r)]
        assert not any(v)
    assert 9*12320==110880 and 2*1455*2>8*693 and 2*2910>58*99
    return True
if __name__=='__main__':
    assert check()
    print('Rank38 {018,024,226,230}: 11576 <= N18 <= 12320, U226 >= 2910, U230 <= 13130.')
