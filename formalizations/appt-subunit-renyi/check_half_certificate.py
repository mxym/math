"""Exact rational Bernstein identity check; not a numerical parameter test."""
from fractions import Fraction as F
from math import comb
import json
from pathlib import Path

def require(ok, msg):
    if not ok: raise ValueError(msg)
def clean(p): return {k:v for k,v in p.items() if v}
def add(p,q):
    out=dict(p)
    for k,v in q.items():out[k]=out.get(k,F(0))+v
    return clean(out)
def mul(p,q):
    out={}
    for (i,j),v in p.items():
        for (k,l),w in q.items():out[(i+k,j+l)]=out.get((i+k,j+l),F(0))+v*w
    return clean(out)
def scale(p,c):return clean({k:v*c for k,v in p.items()})
def power(p,n):
    out={(0,0):F(1)}
    for _ in range(n):out=mul(out,p)
    return out
def substitute(p,r,t):
    out={}
    for (i,j),v in p.items():out=add(out,scale(mul(power(r,i),power(t,j)),v))
    return out

Q={(5,2):F(12),(4,3):F(8),(4,2):F(24),(4,1):F(-4),(3,3):F(16),
   (3,1):F(16),(3,0):F(-8),(2,3):F(8),(2,2):F(-24),(2,1):F(-12),
   (1,2):F(-12),(1,1):F(8),(1,0):F(-8),(0,1):F(-8),(0,0):F(16)}
R={(4,2):F(-12),(3,3):F(-8),(3,2):F(-36),(3,1):F(4),(2,3):F(-24),
   (2,2):F(-36),(2,1):F(-12),(2,0):F(8),(1,3):F(-32),(1,2):F(-12),
   (1,0):F(8),(0,3):F(-32),(0,1):F(-8),(0,0):F(16)}
require(add({(0,3):F(32)},mul({(0,0):F(1),(1,0):F(-1)},R))==Q,'corner identity')

def main():
    boxes=json.loads((Path(__file__).parent/'half_certificate.json').read_text())
    expected=[(0,F(3,4),0,F(1,2),'Q'),(0,F(3,8),F(1,2),1,'Q'),
              (F(3,8),F(3,4),F(1,2),F(3,4),'Q'),(F(3,8),F(9,16),F(3,4),1,'Q'),
              (F(9,16),F(3,4),F(3,4),1,'Q'),(F(3,4),1,F(1,4),1,'Q'),
              (F(3,4),1,0,F(1,4),'R')]
    require(len(boxes)==len(expected),'box count')
    coefficients=0
    for box,cover in zip(boxes,expected):
        r0,r1,t0,t1=map(F,[box['r0'],box['r1'],box['t0'],box['t1']])
        require((r0,r1,t0,t1,box['kind'])==cover,'coverage')
        n,m=box['n'],box['m'];b=box['b']
        require(len(b)==n+1 and all(len(row)==m+1 for row in b),'Bernstein dimensions')
        actual=substitute(Q if box['kind']=='Q' else R,
                          {(0,0):r0,(1,0):r1-r0},{(0,0):t0,(0,1):t1-t0})
        certified={}
        for i in range(n+1):
            for j in range(m+1):
                c=F(b[i][j]);require(c>=0,'negative Bernstein coefficient')
                basis=mul(mul({(i,0):F(comb(n,i))},power({(0,0):F(1),(1,0):F(-1)},n-i)),
                          mul({(0,j):F(comb(m,j))},power({(0,0):F(1),(0,1):F(-1)},m-j)))
                certified=add(certified,scale(basis,c));coefficients+=1
        require(actual==certified,'polynomial identity mismatch')
    print('EXACT_HALF_CERTIFICATE_PASS',len(boxes),'boxes',coefficients,'coefficients; entire continuum certificate')

if __name__=='__main__':main()
