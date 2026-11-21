from fractions import Fraction as F

def check(b, msg):
    if not b:
        raise SystemExit(msg)

s = tuple(map(F, ('.139','.101','.106','.155','.190','.309')))
theta = F(7,32)
I = (
    ((2,1,1,1,0,2), '.499', '.5515'),
    ((2,1,2,0,2,1), '.5405', '.5645'),
    ((2,2,1,0,2,1), '.5555', '.5695'),
    ((1,1,2,1,0,2), '.5655', '.5845'),
    ((1,2,1,1,0,2), '.5805', '.5895'),
)
front = F('.4995')
for assign, lo, hi in I:
    a,b,c=(sum(x for x, j in zip(s, assign) if j==i) for i in range(3))
    lo,hi=F(lo),F(hi)
    check(lo < front < hi, 'interval does not extend previously covered range')
    front=hi
    for d in (lo,hi):
        margins = (
            a, F(2,3)-a-b, c-b, d-c, a+b-d,
            1+d-2*a-3*b,
            2-2*theta+(2+theta)*d-(7-4*theta)*a-(4-theta)*b,
            2+2*d-7*a-4*b-theta,
        )
        check(min(margins)>=F('.00049'), f'Jain rail: {assign} {d} {margins}')

def w(t):
    t=F(t)
    return (1-t)*(1-2*t)**2

check(w('.1011')>F('1.20')*w('.1389'),'marker 2 ratio')
check(w('.1061')>F('1.20')*w('.1389'),'marker 3 ratio')
rho=F('.00000002')
p=F('.4305')+rho
h=1-p
E=F('.3965')+rho
adv=4*p*E/h
comp=3*F('.121')*(1+2*F('1.20'))
check(adv<F('1.200'), 'adverse rank-six coefficient')
check(comp-adv>F('.034'), 'net negative rank-six margin')
print('all rational checks pass')
