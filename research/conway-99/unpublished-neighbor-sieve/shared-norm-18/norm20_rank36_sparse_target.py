"""Graph-wide rank-36 lower for the literal oriented N20 on a sparse face."""
from rank36_four_hit_sets import engine, P

def check():
    R,C,D,o=engine()
    assert P==2402
    nonnegative={
        ('w',(0,22)):1383348281576,('w',(1,21)):2760872328064,
        ('w',(2,26)):13643039573200,('w',(3,35)):2057818539332,
        ('w',(4,44)):2726851399296,'Y1':10652099530709,
        'Y3':1029232897,'N16lift':2958341632,('Ct',48):9810121048,
        ('G',15000):115464}
    omitted={(0,16):47299640960644,(3,37):2730919119040,
             (0,18):29377689600614,(0,24):337382323438,(2,30):2732490738032}
    assert all(c>0 for c in [*nonnegative.values(),*omitted.values()])
    for i,z in enumerate(o):
        assert 2160255457*(P*D[0,20][i]-151373*z) == (2091594937*z
                +sum(c*R[k][i] for k,c in nonnegative.items())
                -61278663343*R['N'][i]-sum(c*D[k][i] for k,c in omitted.items()))
    print('With 016,018,024,230,337 absent at rank 36: oriented N20 >=151374.')
if __name__=='__main__':check()
