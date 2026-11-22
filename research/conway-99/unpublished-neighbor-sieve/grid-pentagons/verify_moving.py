"""Exclude a grid for which its two lines have the same two moving axes at every point."""
from itertools import combinations_with_replacement, permutations, product
from pathlib import Path
import gzip
import json

LINES=[(0,1,2),(3,4,5),(6,7,8),(0,3,6),(1,4,7),(2,5,8)]
PAIRS=list(combinations_with_replacement(range(18),2))


def moves(code):
    maps={}
    for j,(p,q,r) in enumerate(LINES):
        x,y=(0,0) if j<4 else tuple((code>>(2*(j-4)+h))&1 for h in range(2))
        for a,b,d in ((p,q,x),(p,r,y),(q,r,x^y^1)):
            maps[a,b]=maps[b,a]=d
    return maps


def words(code):
    maps=moves(code)
    for s in range(9):
        near=[q for q in range(9) if (s,q) in maps]
        far=[q for q in range(9) if q!=s and q not in near]
        diagonals=[]
        for perm in permutations(range(3)):
            triple=[3*i+j for i,j in enumerate(perm)]
            if s in triple:diagonals.append([q for q in triple if q!=s])
        assert len(diagonals)==2 and sorted(sum(diagonals,[]))==far
        for axis in range(2):
            owner=2*s+axis
            base={owner}|{2*q+(axis^maps[s,q]) for q in near}
            for opposite in diagonals:
                for labels in product(range(2),repeat=2):
                    yield owner,base|{2*q+a for q,a in zip(opposite,labels)}
        for labels in product(range(2),repeat=4):
            yield None,{2*q+a for q,a in zip(far,labels)}
        for opposite in diagonals:
            yield None,{2*q+a for q in opposite for a in (0,1)}


def main():
    path=Path(__file__).with_name('moving-pair-cert.json.gz')
    with gzip.open(path,'rt') as f:
        certs=json.load(f)
    assert set(certs)==set(map(str,range(16)))
    for code in range(16):
        entries=certs[str(code)]
        assert all(0<=j<len(PAIRS) and v for j,v in entries)
        assert len(set(j for j,v in entries))==len(entries)
        support=[(*PAIRS[j],v) for j,v in entries]
        required=sum(v*(8+24*(a==b)-4*(a//2==b//2)) for a,b,v in support)
        assert required>0
        count=0
        for owner, selected in words(code):
            score=sum(v*(int(a in selected)+int(a==owner)) for a,b,v in support if b in selected)
            assert score<=0
            count+=1
        assert count==306
    print('Verified the moving-pair contradiction for all 16 tables and 306 words per table.')


if __name__=='__main__':main()
