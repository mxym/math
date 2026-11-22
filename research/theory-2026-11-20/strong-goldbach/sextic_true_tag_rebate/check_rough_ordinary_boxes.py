from functools import lru_cache
from itertools import combinations,product
from contextlib import redirect_stdout
from fractions import Fraction as Q
from io import StringIO
from pathlib import Path
from runpy import run_path
D=2560000
A=320256
scale=10**15
D2=D**2
D5=D**5
D6=D5*D
def repetitions(*j):
    result=run=1
    for a,b in zip(j,j[1:]):
        if a==b:
            run+=1
            result*=run
        else:
            run=1
    return result
def upward(n,d): return (n+d-1)//d
def rank4():
    count=mass=0
    h=4996
    h3=h**3*scale
    vertices=tuple(product((0,h),repeat=3))
    for i in range(129):
        x=A+h*i
        for j in range(i,(256-i)//3+1):
            y=A+h*j
            for k in range(j,(256-i-j)//2+1):
                z=A+h*k
                count+=1
                v=max((x+a)**2+(y+b)**2+(z+c)**2+(D-x-y-z-a-b-c)**2 for a,b,c in vertices)
                n=1680*v-528*D2
                if n>0:
                    mass+=upward(n*h3,D5*repetitions(i,j,k))
    return count,mass
@lru_cache(None)
def f(q):
    z=D-2*q
    return z**4*(11*D2-7*z*z) if z>0 else 0
@lru_cache(None)
def psi(q):
    return f(q) if 2*q<=D else -f(D-q)
def rank5():
    h=3745
    h4=h**4*scale
    mass=count=0
    for i in range(129):
        x=A+h*i
        for j in range(i,(256-i)//4+1):
            y=A+h*j
            for k in range(j,(256-i-j)//3+1):
                z=A+h*k
                for l in range(k,(256-i-j-k)//2+1):
                    count+=1
                    w=A+h*l
                    S=x+y+z+w
                    v=max(w,D-S-4*h)
                    n=f(x)+f(y)+f(z)+f(w)+f(v)-4*D6
                    n-=sum(psi(p+q+2*h) for p,q in combinations((x,y,z,w),2))
                    n-=sum(psi(D-S+p) for p in (x,y,z,w))
                    if n>0:
                        mass+=upward(n*h4,4*D5*x*y*z*w*v*repetitions(i,j,k,l))
    return count,mass
if __name__=="__main__":
    ans=(rank4(),rank5())
    if ans!=((123464,5455365940837),(1673243,11092191776369)):
        raise ArithmeticError("mass ceilings mismatch")
    m4,m5=(Q(row[1],scale) for row in ans)
    m=(m4,m5,Q(451,10**6),Q(1671,10**9))
    with redirect_stdout(StringIO()):
        rs=run_path(str(Path(__file__).with_name("check_joint_rough_marks_v4.py")))
    u=rs["U"]
    m_total=sum(m)
    debit=2*m_total+sum(min(m[i]*u[j],m[j]*u[i])
                        for i in range(4) for j in range(4))
    if not (m4<Q(5456,10**6) and m5<Q(11093,10**6)
            and debit<Q(46,1000) and 156*m_total<Q(268,100)):
        raise ArithmeticError("rough or tiny debit failed")
    print("ordered box counts and ceilings per 10^15:",ans)
    print("same physical rough debit upper:",float(debit))
    print("leading true tiny-union debit coefficient upper:",float(156*m_total))
