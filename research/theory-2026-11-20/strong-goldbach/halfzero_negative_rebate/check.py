from fractions import Fraction as F
from sys import argv

def need(b,name):
    if not b: raise ArithmeticError(name)

n=int(argv[1]) if len(argv)>1 else 1024
need(n>=8 and n%2==0,"grid")
S=10**20
def up(num,den):
    return (S*num+den-1)//den

# Sort a as the largest of the arguments a,b,c=1-2u.
# Coarea normalizer after choosing its position and writing b=(1-a)t
# is 1/((1-b)(1-c)).
D=3*n*n
D2=D*D; D4=D2*D2
def g(i):
    i2=i*i
    return 80*i2*(31*D2-20*i2)
ng=0
for i in range(n):
    al=(n+2*i)*n; ah=al+2*n
    dl=(3*n-(n+2*i+2)); dh=dl+2
    g0=961*D4 if 40*al*al<=31*D2<=40*ah*ah else max(g(al),g(ah))
    mc=min(ah,D//2)
    for j in range(n):
        bl=dl*j; cl=dl*(n-j-1)
        if bl>ah or cl>ah: continue
        bh=min(mc,dh*(j+1)); ch=min(mc,dh*(n-j))
        h=g0+g(bh)+g(ch)-880*D4
        if h>0:
            ng += up(2*h,3*n*n*1600*D2*(D-bh)*(D-ch))
# Giant: s,t in [0,1/2], use t symmetry; integrand 8s/(1-s) times
# max(0, r-31/20-(63/20)(r-7/3)_+).
D=2*n;D2=D*D;D4=D2*D2
def r(s,t):
    return 6*(D-s)**2*D2+2*s*s*(t*t+(D-t)**2)
def h0(R):
    return max(0,3*(20*R-31*D4) if 3*R<=7*D4 else 3*(116*D4-43*R))
gg=0
for i in range(n):
    for j in range(n):
        rl=r(i+1,j+1); rh=r(i,j)
        h=47*D4 if 3*rl<=7*D4<=3*rh else max(h0(rl),h0(rh))
        if h:
            gg += up(8*(i+1)*h,4*n*n*(D-i-1)*60*D4)
ng=F(ng,S);gg=F(gg,S)
a=F(74161,100000)
need(a*a<F(11,20),"positive semiprime cutoff")
semi=2*((1-a**3)/3-a*a*(1-a))
tail=F(31,20)*(F(".01661")+F(".01824")+F(".0201"))+F(".00163")
upper=F("3.446")*(ng+gg+semi+tail)
rebate=(F("1.8")-upper)/F("4.2")
print("grid",n,"non-giant upper",float(ng),"giant upper",float(gg),"semi upper",float(semi))
print("whole unwanted upper",float(upper),"normalized rebate >",float(rebate))
if len(argv)==1:
    need(rebate>F(".062"),"actual rebate strict margin")
