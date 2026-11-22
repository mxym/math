"""Exact Rosser/Buchstab scalar certificate.  Run python3 -O -B check.py."""
from fractions import Fraction as Q

def demand(x, why):
    if not x:
        raise ArithmeticError(why)

def log_bounds(u,n=16):
    a=(u-1)/(u+1)
    demand(0<=a<1, 'positive log series')
    low=2*sum((a**(2*j+1)/(2*j+1) for j in range(n)),Q(0))
    return low,low+2*a**(2*n+1)/((2*n+1)*(1-a*a))

T=Q(7,32)
alpha=Q(1001,1000)
D=Q(111,200)
a0=Q(9,80)
step=Q(1,4000)
S=10**18

def ceilq(z):
    return (z.numerator+z.denominator-1)//z.denominator

def flr(z):
    return z.numerator//z.denominator

def main():
    # sF(s)=2 e^gamma [1+∫_{3}^{s} log(v−2)/(v−1) dv]
    # for s in [3,5]. The integrand increases: derivative sign is
    # (v−1)/(v−2)−log(v−2) ≥4/3−log 3>0.
    demand(log_bounds(Q(3))[1]<Q(4,3),'upper quadrature monotone')
    sf=D/a0
    demand(3<sf<5,'base F(s) range')
    K=4096
    h=(sf-3)/K
    upp=0
    for j in range(1,K+1):
        v=3+j*h
        upp+=ceilq(S*h*log_bounds(v-2)[1]/(v-1))
    base=2/D*(1+Q(upp,S))
    # 340 independent marked quotient lower sieves.
    total=0
    min_sample,max_sample=Q(4),Q(2)
    for j in range(340):
        a=a0+j*step
        b=a+step
        cap=min((1+a)/2,(1-(Q(3,2)-2*T)*b)/(1+T),1-(alpha*T+3*b)/2)
        virtual=cap-Q(7,100000)
        total_level=cap-Q(15,100000)
        residual=total_level-b
        s=residual/b
        demand(2*s>4 and s<4,'marked lower f(s) interval')
        demand(2*b<total_level and residual>2*b,'marked first-square reserve')
        demand(total_level+Q(2,100000)<virtual<cap,'packing slack')
        demand(b<=Q(1975,10000),'bounded marked support')
        sell=2/residual*log_bounds(s-1)[0]*log_bounds(b/a)[0]
        total+=flr(S*sell)
        min_sample=min(min_sample,s)
        max_sample=max(max_sample,s)
    removal=Q(total,S)
    demand(base<Q(50017,10**4),'unmarked upper')
    demand(removal>Q(155617,10**5),'real marked lower')
    demand(base-removal<Q(3446,1000),'actual prime upper coefficient')
    # pi < 22/7 suffices for the stated native two-rank consequence.
    demand(Q(554,1000)*(2+4*log_bounds(Q(2))[0]-Q(22,7)**2/6)>Q(173,100),
           'true native two-rank coefficient')
    print('exact base upper:',float(base))
    print('exact marked removal lower:',float(removal))
    print('difference:',float(base-removal),'s_j:',float(min_sample),float(max_sample))

if __name__=='__main__': main()
