"""Direct Gaussian-integer matrix replay; exact comparisons of quadratic surds."""
from random import Random
from itertools import product
rng=Random(20829)
def add(a,b):return (a[0]+b[0],a[1]+b[1])
def neg(a):return (-a[0],-a[1])
def conj(a):return (a[0],-a[1])
def mul(a,b):return (a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])
def norm(a):return a[0]**2+a[1]**2
def mm(a,b):return tuple(add(mul(a[2*i],b[j]),mul(a[2*i+1],b[2+j])) for i in range(2) for j in range(2))
def adj(a):return tuple(conj(a[2*j+i]) for i in range(2) for j in range(2))
def plus(a,b):return tuple(add(x,y) for x,y in zip(a,b))
def herm(u,v,z,w):return ((u,0),(z,w),(z,-w),(v,0))
def ask(c,msg):
    if not c:raise ValueError(msg)
def sig(x):return (x>0)-(x<0)
def cmp(x,v,y,w): # x+sqrt(v) versus y+sqrt(w)
    if x>y:return -cmp(y,w,x,v)
    if x==y:return sig(v-w)
    D=y-x; E=v-w-D*D
    return -1 if E<0 else sig(E*E-4*D*D*w)
def inv(a):
    ask(a==adj(a),'not Hermitian');t=a[0][0]+a[3][0]
    return t,(a[0][0]-a[3][0])**2+4*norm(a[1])
def det(a):return add(mul(a[0],a[3]),neg(mul(a[1],a[2])))
Id=herm(1,1,0,0)
cases=[]
for _ in range(420):
    vals=[rng.randrange(-4,5) for j in range(8)]
    cases.append((herm(*vals[:4]),herm(*vals[4:])))
for u,v in product(range(-3,4),repeat=2):
    a=herm(u,v,0,0);cases.append((a,a));cases.append((a,herm(0,0,0,1)))
count=failed=0
for a,b in cases:
    t=q=Id;h=plus(a,b); twice_c=inv(h)[0];com=mm(a,b)==mm(b,a)
    for k in range(1,19):
        q=plus(mm(a,q),mm(q,b));t=mm(h,t)
        # All matrices are doubled consistently to clear Re denominators.
        r=plus(q,adj(q));s=plus(q,q);u,v=inv(r); U,V=inv(plus(t,t))
        ask(cmp(abs(u),v,abs(U),V)>=0,'singular first partial H vs R')
        ask(max(u*u,v)>=max(U*U,V),'singular second partial H vs R')
        e,f=inv(mm(adj(s),s));g=norm(det(s))
        # Compare squared operator and trace norms, not merely tests against H eigenvectors.
        ask(cmp(2*e,4*f,u*u+v,4*u*u*v)>=0,'singular first partial R vs Q')
        ask(cmp(e,4*g,max(u*u,v),0)>=0,'singular second partial R vs Q')
        good=cmp(u,v,U,V)>=0 and u>=U
        expected=k%2==0 or k<5 or com or twice_c>=0
        ask(good==expected,'signed criterion')
        if not good:ask(u<U,'unfavorable trace');failed+=1
        count+=1
print(f'PASS {count} orders of Gaussian-integer Hermitian 2x2 pairs via Q_next=AQ+QB: both singular partial sums on both legs and signed criterion; {failed} negative signed trace cases.')
