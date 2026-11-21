"""Exact exponent rails for GiantReflectedSupercriticalTransfer.md."""
from fractions import Fraction as F
from itertools import product


def need(test, msg):
    if not test:
        raise ArithmeticError(msg)


theta = F(7,32)
D = F(".001")
S = tuple(map(F,(".101",".109")))
A = tuple(map(F,(".415",".425")))
B = tuple(map(F,(".985",".992")))
rows=[]
for s,a,b,d,e in product(S,A,B,(F(0),D),(F(0),D)):
    v = 1-b-e
    base = v+d+5*s+2*a
    gaps = (v-d, 1-2*v-s-2*a, 2-(theta+base),
            2-(2*theta*(v+a-s)+base), a+s-F(".5"), a+b-1)
    need(all(g>0 for g in gaps), 'failed physical rail')
    rows.append(gaps)
mins = tuple(min(row[i] for row in rows) for i in range(6))
need(mins == tuple(map(F,(".006",".011",".37025",".4441875",".016",".4"))),
     'claimed rail values')
need(F("1.561")+theta<2 and F("1.561")+F(".7")*theta<2, 'general spare rails')
print('32 exact corners, gaps:', *(str(x) for x in mins))
