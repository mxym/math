
from math import comb
from fractions import Fraction as F

def gegen(m,x):
    a,b=0.,1.
    for j in range(m):
        a,b=b,((2*j+5)*x*b-j*a)/(j+5)
    return b

Q=1<<24
def evaluate(b,k,q):
    # Homogenized evaluation at z=-k/(Q-k). Use only integers.
    u=-k; v=q-k; y=b[-1]; p=v
    for c in b[-2::-1]:
        y=y*u+c*p; p*=v
    return y

def check():
    roots=[]; count=0
    tiny={2:[0,310,512],3:[0,195,293,512],4:[0,129,188,357,512],
          5:[0,88,131,273,401,512],6:[0,62,98,211,332,428,512]}
    for N in range(2,200):
        m=N-1
        nextroots=[]
        points=[-1.0,*roots,1.0]
        for a,b in zip(points,points[1:]):
            fa=gegen(m,a)
            for _ in range(37):
                c=(a+b)/2; fc=gegen(m,c)
                if fa*fc<=0:
                    b=c
                else:
                    a=c; fa=fc
            nextroots.append((a+b)/2)
        roots=nextroots
        a=[comb(N,i)*(2*N*(1<<N)-i*(1<<N)-i*(1<<(N+1-i))) for i in range(N+1)]
        b=[v*v-(a[i-1]*a[i+1] if 0<i<N else 0) for i,v in enumerate(a)]
        ks=[0,*[round((1-x)*Q/2) for x in roots[::-1]],Q]
        q=Q
        if N in tiny: ks=tiny[N]; q=512
        if not all(x<y for x,y in zip(ks,ks[1:])): raise AssertionError(("order",N))
        for i,k in enumerate(ks):
            if ((-1)**i)*evaluate(b,k,q)<=0: raise AssertionError(("sign",N,i,k))
            count+=1
        if N%25==0: print("through",N,"signs",count,flush=True)
    assert count == 20097
    print("PASS exact finite Jacobi sign witnesses",count,flush=True)
def exp_bounds(x): # 0<=x<=1, rigorous rational bounds
    a=t=F(1)
    for n in range(1,8):
        t=t*x/n; a+=t
    return a,a+(t*x/8)/(1-x/9)

def bounds():
    nu=F(403,400); c=F(19,10)
    assert F(15,4)>c*c
    b=F(1)/c
    assert c+F(3,2)+b-b**3/3>2*c*nu
    assert F(10,7)**2>2 and F(17,10)**4>8
    d=F(269,250)
    assert d*d>1+(F(3)/(4*c))**2
    e1=exp_bounds(F(6,25))[1]; e2=exp_bounds(F(3,10))[1]
    assert F(3,16)*(1+F(10,7))/c < F(6,25)
    assert F(9,16)/c < F(3,10)
    assert e1*d*F(17,10) < F(7,3) and e2*d*3 < F(9,2)
    elo=exp_bounds(F(1))[0]; ehalf=exp_bounds(F(1,2))[0]
    assert 2/elo<F(37,50) and 1/ehalf<F(61,100) and 4/(3*elo)<F(1,2)
    assert F(1,2)+(F(13,2)+F(21,16))/200+F(7,4)*nu*F(23,100)<F(19,20)
    assert F(23,100)**2>F(1,19)
    assert F(7,3)/elo<F(43,50)
    assert (F(1,2)+F(13,400))*F(10,19)<F(2,7)
    assert (4*nu)**2/380<F(21,100)**2
    assert F(7,3)*(F(2,7)*F(37,50)+F(3,200)+F(21,100)*F(61,100))<F(43,50)
    assert 1+F(3,400)+nu/3<F(27,20)
    assert F(9,2)*F(27,20)*F(10,37)/400<F(1,200)
    assert F(43,50)+F(1,200)<F(22,25)
    assert F(1,2)+F(13,400)+F(7,4)*(F(1,2)+F(3,400))<F(3,2)
    assert 2+F(6,200)<F(21,10) and 1+F(3,400)+nu<3
    assert F(7,3)*F(321,10)/2**10+F(27,2)/2**15<F(1,4)
    print("PASS exact rational analytic bounds")

if __name__=="__main__":
    if not __debug__: raise RuntimeError("run with ordinary Python, not python -O")
    bounds()
    check()

