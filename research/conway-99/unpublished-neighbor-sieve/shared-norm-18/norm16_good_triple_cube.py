"""Exact rank-36 population rows. Run next to rank36_four_hit_sets.py."""
from rank36_four_hit_sets import engine, P

def check():
    R,C,D,o=engine()
    assert P==2402
    def row(weights,constant,proof):
        assert all(v>0 for v in weights.values())
        assert all(v>0 for v,k in proof if k!='N')
        assert all(sum(P*z*D[k][i] for k,z in weights.items())-constant*o[i]
                   ==sum(z*R[k][i] for z,k in proof) for i in range(len(o)))
    row({(0,16):18292,(0,18):4707,(0,20):678,(0,26):117,
         (1,21):1090,(1,25):428,(2,26):60,(2,30):448},125821140,
        [(2032092,('w',(0,22))),(2618180,('w',(2,28))),
         (1124136,('w',(3,35))),(12010,('w',(4,46))),
         (562068,'S'),(4907301,'Y1'),(1029,'Y3'),(-53175,'N')])
    # The second inequality uses 29372-G121 >=0.
    cap='true G121 cap'
    R[cap]=[29372*x-P*y for x,y in zip(o,D[1,21])]
    row({(0,16):3312,(0,18):687,(0,26):7,(1,25):56},4747792,
        [(120100,('w',(0,22))),(67256,('w',(2,22))),
         (172944,('w',(3,33))),(168140,('w',(3,35))),
         (33628,('w',(4,44))),(67256,'S'),(365890,'Y1'),
         (168,'Y2'),(189,'Y3'),(70,cap),(-10010,'N')])
    assert 128*6496<=30*27720<128*6497
    assert 18292*6878<125821140<=18292*6880
    assert 125821140-18292*6496==6996308
    return True

if __name__=='__main__':
    assert check()
    print('Rank 36: exact norm-16 lower 6880 contradicts graph cap 6496 on the five-type containment.')
