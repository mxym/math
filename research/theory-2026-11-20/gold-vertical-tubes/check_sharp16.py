"""Direct GF16 rank-two orbit and endpoint witness check."""
from itertools import combinations

def mul(x,y):
    z=0
    while y:
        if y&1:z^=x
        y>>=1;x<<=1
        if x&16:x^=19
    return z

def square(x):return mul(x,x)
def cube(x):return mul(x,square(x))
def tr(x):
    a=square(x);b=square(a);c=square(b)
    out=x^a^b^c
    if out not in (0,1):raise ValueError('trace')
    return out

def require(x):
    if not x:raise ValueError('root check')

W=frozenset([0,1,8,9])
perp=lambda V:frozenset(x for x in range(16) if all(tr(mul(x,y))==0 for y in V))
all_W={frozenset((0,x,y,x^y)) for x,y in combinations(range(1,16),2)}
cub={cube(x) for x in range(1,16)}
good={X for X in all_W if not (perp(X)&cub)}
orb=set()
for j in range(4):
    for f in cub:
        orb.add(frozenset(mul(f,a) for a in W))
    W=frozenset(square(a) for a in W)
require(len(all_W)==35 and len(cub)==5 and good==orb and len(orb)==10)
pts=[0,1,2,99,68,181,6,40,249,234,219,140,61,14,207,16,129,150]
require(len(pts)==len(set(pts))==18)
require(all((x//16)^cube(x%16) in W for x in pts))
require(len({x^y for x,y in combinations(pts,2)})==153)
for a in range(1,16):
    hist={}
    for x in range(16):
        d=cube(x)^cube(x^a)
        q=min(d^w for w in W);hist[q]=hist.get(q,0)+1
    require(sorted(hist.values())==[4]*4)
print('PASS: 18 actual GF16 tube points, 153 distinct pair sums; exact 10 one-orbit parameters.')
