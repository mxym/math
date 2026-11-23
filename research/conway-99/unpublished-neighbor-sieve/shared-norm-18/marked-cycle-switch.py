"""Determine all cycle length / C occupancy decks passing the exact cycle gap.
The tests are necessary, not sufficient for graph existence.
"""
from fractions import Fraction as F

def partitions(n, rem, previous, delta):
    if n == 0:
        if not rem:
            yield ()
        return
    for k in range(previous[0], n + 1):
        if k == 4:
            continue
        for j in range(min(k // 2, rem) + 1):
            if (k, j) < previous or 2*(rem-j) > n-k:
                continue
            if delta==12 and (k,j)==(3,0):  # previously excluded triangle flip
                continue
            for tail in partitions(n-k, rem-j, (k,j), delta):
                yield ((k,j),) + tail

def valid(deck, delta):
    disc = 154*22 - (3*delta-22)**2
    # Nonconstant weights of range 1 are indicators of proper nonempty unions.
    states = {(0, 0)}
    for k,j in deck:
        states |= {(a+k, b+j) for a,b in states}
    for k,j in states:
        if k not in (0,33) and 10*(disc*k*(33-k)-42*(33*j-delta*k)**2) <= 23*33*disc:
            return False
    h = 1 - F(1386,disc)*sum(F((33*j-delta*k)**2, 33**2*k) for k,j in deck)
    assert F(27,2)*h > F(23,10)
    if 6*h > F(23,10):
        return True
    # Range 2: test the sufficient statistics sum kf, sum jf, sum kf² and support.
    states = {(0,0,0,0)}
    for k,j in deck:
        states = {(a+i*k,b+i*j,c+i*i*k,mask | 1<<i)
                  for a,b,c,mask in states for i in (0,1,2)}
    return all(10*(disc*(33*c-a*a)-42*(33*b-delta*a)**2)>23*33*disc
               for a,b,c,mask in states if (mask & 5)==5)

for delta,new,old in ((5,7089,7138),(12,2494,2503)):
    decks = list(partitions(33,delta,(3,0),delta))
    assert len(decks)==old and sum(valid(t,delta) for t in decks)==new
    print('overlap',delta,':',old,'initial formal cycle decks,',new,'pass every integer cycle-weight test')
