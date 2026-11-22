"""Outward rational enclosure for the four-least rank 5–7 debit."""
from fractions import Fraction as F
from math import comb

def need(p, tag):
    if not p:
        raise ArithmeticError(tag)

def up(num, den):
    return -(-num//den)

H, SCALE, I = 200, 10**15, 67000
b = [0 if i<H else up(SCALE*H,i) for i in range(I+1)]
for k in (2,3):
    pref = [0]
    for y in b:
        pref.append(pref[-1]+y)
    b = [0 if i+1<k*H else up(pref[i+1-H],i) for i in range(I+1)]
# b[i]/SCALE bounds b_3(t) on [i/H,(i+1)/H).
levels = [b]
while 2**len(levels) <= len(b):
    old = levels[-1]
    step = 2**(len(levels)-1)
    levels.append([max(old[i],old[i+step]) for i in range(len(old)-step)])

def sup3(l,r):
    il, ir = int(H*l), int(H*r)
    need(0<il<=ir<=I, "Buchstab lookup")
    power=(ir-il+1).bit_length()-1
    m=max(levels[power][il],levels[power][ir-2**power+1])
    return F(m,SCALE)

def IH(t):
    return sum((-1)**j*comb(3,j)*max(t-j,0)**3 for j in range(4))/6

a, cap, theta=F(".003"),F(".080"),F(".499")
mass5=mass6=mass7=U=F(0)
for p in range(385):
    vl, vu=a+F(p,5000), a+F(p+1,5000)
    vol0=(vu-a)**3/6*(vu-vl)
    for j in range(120):
        zl,zu=F(j,40),F(j+1,40)
        vol=vol0*(IH(zu)-IH(zl))
        tl,tu=1-vu-3*a-(vu-a)*zu,1-vl-3*a-(vl-a)*zl
        need(tl>3*vu, "quotient simplex")
        need(3360*4*vu**2-1056<0, "rank5 monotonicity")
        mass5 += vol*(10080*tu+(3360*4*vu**2-1056)/tu)
        mass6 += vol*20160*(tu-2*vl)
        mass7 += vol*(2112*sup3(tl/vu,tu/vl)/vl
                      +20160*(tu-3*vl)**2/tu)
        D=theta-(1-tl)
        need(D>2*vu, "true lower floor for upper linear sieve")
        if D>=4*vu:
            receiver=F(".575")/vl
        elif D>=3*vu:
            receiver=2/(3*vl)
        else:
            receiver=max(2/(3*vl),2/D)
        U += vol*(2112+8960*tu**2)*receiver
need(vu==cap and zu==3, "complete physical angles")
mass=mass5+mass6+mass7
need(mass<F(".0554") and U<F(".1212"), "angular upper")
m0, U0 = F(".0554"), F(".1212")
cost = (2*((1+F(".228")+F(".007445"))*m0
           + U0*(F(".01701")+F(".16921")+F(".009042")))
        + U0*m0)
need(cost==F(".1909332948") and cost<F(".191"), "full signed union")
print("ordinary rank 5, 6, 7 uppers =",float(mass5),float(mass6),float(mass7))
print("total ordinary =",float(mass), "genuine receiver =",float(U))
print("full union debit <=",float(cost),"< .191")
