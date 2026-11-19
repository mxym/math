"""Exact, finite checks for the angle and kernel calculations, not proof by sampling."""
from fractions import Fraction as F
from itertools import accumulate, combinations

def require(x):
    if not x: raise ArithmeticError("exact check failed")

# Put pi=64 angle units. Use cumulative sums of the sorted smallest entries
# (a separate weak-supermajorization test), not the proof's transfer cases.
P=64; cnt=changed=0
for a in range(1,P):
    for b in range(a,P):
        for c in range(b,P-a-b):
            d=P-a-b-c
            old=sorted(min(i,P-i) for i in (a,b,c))
            new=sorted(min(i+d,P-i-d) for i in (a,b,c))
            require(all(j>=i for i,j in zip(accumulate(old),accumulate(new))))
            require(tuple(old)!=tuple(new))
            # f(x)=(pi/2-x)^2: symmetric-extension angular cost.
            require(sum((P-2*x)**2 for x in new)<sum((P-2*x)**2 for x in old))
            cnt+=1;changed+=int(min(c+d,P-c-d)<min(c,P-c))
print("nondegenerate triangle angle profiles / largest-angle losses:",cnt,"/",changed)

# Independently differentiate g=(1-w)/w with t=-log sin u; w_t=w^3-w.
cnt=0
for j in range(1,31):
    w=F(j,31); wt=w**3-w
    g=(1-w)/w; gt=-wt/(w*w)
    gtt=-(3*w*w-1)*wt/(w*w)+2*wt*wt/(w**3)
    require(gt/g==1+w)
    for m in range(-12,13):
        cot=F(m,7)
        log_uu=(gtt/g-(gt/g)**2)*cot**2+(gt/g)*(1+cot**2)
        require(log_uu==1+w+(1+w**3)*cot**2 and log_uu>0)
        cnt+=1
print("exact log-curvature evaluations:",cnt)

# Finite cyclic gap averages underlying the circle energy step.
cnt=0
for n in range(2,7):
    for x in combinations(range(13),n):
        y=x+tuple(13+t for t in x)
        for k in range(1,n):
            require(sum(y[i+k]-y[i] for i in range(n))==13*k)
            cnt+=1
print("cyclic forward-gap identities:",cnt)
