from fractions import Fraction as F
from math import factorial as fac, isqrt
from itertools import product
from pathlib import Path
from hashlib import sha256
import tempfile, subprocess
from math import nextafter, inf
p=Path(__file__).resolve().with_name('check_full_one_by_one.py')
raw=p.read_bytes()
if sha256(raw).hexdigest() != '3c2328333a931defbb7f1ddf3f0a62ed18d1b2b9e48aa922ee83a4153c4ca9c6':
    raise ArithmeticError('different audited one-by-one checker')
head,a,part=raw.decode().partition('\ntext+=r"""')
pre,b,tail=part.partition('\nint main(){')
if not (a and b):
    raise ArithmeticError('ambiguous audited helper boundary')
env={"__file__":str(p)}
exec(compile(head,str(p),'exec'),env)
text=env['text']+pre
text+=r"""
int main(){
 static_assert(numeric_limits<double>::is_iec559);
 if(fesetround(FE_TONEAREST))abort();
 sieve_constants(); prep_b(800); lin_sieve(); rough2_den();
 const int TR=2,ST=1,MAX=4900;
 I totalL=0,totalU=0,tE=0,tO=0;
 for(int t=30;t<800;t+=TR){
   int th=min(t+TR,800);
   I tV=I(t,th)/P, wT=I(th-t)/P;
   I g0=profile_cell(tV,0);
   I L=lfn[4990-th]*g0,U=ufn[4990-th]*g0;
   I eU=0,oU=0;
   for(int s=800;s<5000;s+=ST){
      int sh=s+ST;
      I W=I(sh-s)/P;
      I g=profile_cell(tV,I(s,sh)/P);
      I e=fplus((pf[0][s]-pf[1][s])/2);
      I o=fplus((pf[0][s]+pf[1][s])/2);
      int r=th+sh;
      if(r<=MAX){
        int D=4990-r;
        I k=lfn[D],u=ufn[D];
        L=L+g*(k*e-u*o)*W;
        U=U+g*(u*e-k*o)*W;
      }else{
        eU=eU+g*e*aff[r]*W;
        oU=oU+g*o*aff[r]*W;
      }
   }
   totalL=totalL+wT*L;totalU=totalU+wT*U;
   tE=tE+wT*eU;tO=tO+wT*oU;
 }
 if (!(totalL.l> -1.275137 && totalU.r< -.2407793 && tE.r<.00245378 && tO.r<.00245645))abort();
 printf("signed coeff [%.14f,%.14f], tails even %.14f odd %.14f\n",totalL.l,totalU.r,tE.r,tO.r);
}
"""
with tempfile.TemporaryDirectory() as d:
    src=Path(d)/'proof.cpp'; out=Path(d)/'proof'
    src.write_text(text)
    subprocess.run(['g++','-O3','-std=c++17','-fno-fast-math','-ffp-contract=off',str(src),'-o',str(out)],check=True)
    subprocess.run([str(out)],check=True)
n=512; D=25*n; A=2*n; h=17; vtx=tuple(product((0,h),repeat=3)); scale=10**15
M4lo,M4hi=0,0
for i in range(n//4+1):
 x=A+i*h
 for j in range(i,(n-i)//3+1):
  y=A+j*h
  for k in range(j,(n-i-j)//2+1):
   z=A+k*h
   fact=6 if i==k else (2 if i==j or j==k else 1)
   cx,cy,cz=2*x+h,2*y+h,2*z+h
   cw=2*D-cx-cy-cz
   # x,y,z,w numerators on the doubled grid. The tangent min is q(c) - radius times L1 gradient.
   qlo=cx*cx+cy*cy+cz*cz+cw*cw-2*h*(abs(cx-cw)+abs(cy-cw)+abs(cz-cw))
   den=D**5*fact
   C=scale*h**3
   M4hi+=(max(0,528*4*D*D-1680*qlo)*C+4*den-1)//(4*den)
   if i+j+2*k+4>n:continue
   qhi=max((x+a)**2+(y+b)**2+(z+c)**2+(D-x-y-z-a-b-c)**2 for a,b,c in vtx)
   M4lo+=max(0,528*D*D-1680*qhi)*C//den
M4lo=F(M4lo,scale);M4hi=F(M4hi,scale)
a=F('.08')
V4= (1-4*a)**3/(fac(4)*fac(3))
q4=4*a*a+2*a*(1-4*a)+F(2,5)*(1-4*a)**2
sig=M4lo-(528-1680*q4)*V4

# Outward real harmonic b_j = kappa_a^{*j}/j!, and the exact signed
# rank-five sum obtained by pairing each divisor with its complement.
dd=lambda x:nextafter(x,-inf)
uu=lambda x:nextafter(x,inf)
def add(x,y): return dd(x[0]+y[0]),uu(x[1]+y[1])
def sub(x,y): return dd(x[0]-y[1]),uu(x[1]-y[0])
def mul(x,y):
    q=[a*b for a in x for b in y]
    return dd(min(q)),uu(max(q))
def div(x,y):
    if not y[0]>0: raise ArithmeticError('nonpositive interval denominator')
    return mul(x,(dd(1/y[1]),uu(1/y[0])))
def rat(n,d=1):
    q=n/d
    return dd(q),uu(q)
P=10000; fl=800
D=[]
for j in range(1,6):
    d=[(0.,0.)]*(P+1)
    for i in range(j*fl,P+1):
        t=dd(i/P),uu((i+1)/P)
        d[i]=div((1,1),t) if j==1 else div((max(0.,p[i-fl][0]),p[i-fl+1][1]),t)
    p=[(0.,0.)]
    for v in d: p.append(add(p[-1],div(v,(P,P))))
    D.append(d)
def value(i):
    y=max(0,P//2-i)
    return rat(y**4*(44*P*P-112*y*y),P**6)
def psi(i): return sub(value(i),value(P-i))
m5=min(D[4][P-1][0],D[4][P][0]),max(D[4][P-1][1],D[4][P][1])
for i in range(800,6800):
    v=psi(i+1)[0],psi(i)[1]
    m5=sub(m5,div(mul(v,mul(D[0][i],D[3][P-i-1])),(P,P)))
for i in range(1600,7600):
    v=psi(i+1)[0],psi(i)[1]
    m5=add(m5,div(mul(v,mul(D[1][i],D[2][P-i-1])),(P,P)))
if not F(m5[1]) < F('-.0877432'):
    raise ArithmeticError('rank-five lower mass')

def ph(u):
    h2=u.numerator*10**12//u.denominator
    root=F(isqrt(h2)+1,10**6)
    return 10080*root-1056/root
K4=max(max(F(0),1680*F(j+1,1000)-528)*F(j+1,1000)*(1-F(j,1000))**3/27
       for j in range(250,760))
K5=max(max(F(0),ph(F(j+1,1000)))*F(j,1000)*((1-F(j,1000))/4)**4
       for j in range(200,680))
K6=F(40320,6**6)
K7=F(2112,7**4)+F(80640,7**7)*F('3.742')
if not (F('3.742')**2 > 14 and max(K4,K5,K6,K7)<F('1.25')):
    raise ArithmeticError('low negative cap')
absX1=F('.575')/F('.08')*(F('.037')*90+F('.04')*41)
def ahi(k): return F(1056*2**(k-5),k**3)+F(80640*2**(k-7),k**5)
if not (max(ahi(k) for k in [8,10])<41 and ahi(12)<90 and absX1<36):
    raise ArithmeticError('whole one-tag absolute cap')
a=F('.08')
high=sum((F(1056*2**(j-5),j**4)+F(80640*2**(j-7),j**6))*(1-j*a)**(j-1)
         /(fac(j)*fac(j-1)*a**j) for j in [9,11])
m6=F(40320)*(1-6*a)**5/(fac(6)*fac(5))
m7=F(80640)*(1-7*a)**6/(fac(7)*fac(6))
neg=sig+m6+m7-F('.01701')+F('.0877432')
tol=2*(F('1.275137')*M4hi+F('.422')*F('.00245645')+F('1.25')*F('.00245378')
       -F('.2407793')*neg+36*high)
if not (M4hi==F('0.061684801406559') and neg>F('.16332506') and tol<F('.092')):
    raise ArithmeticError('whole high-rank zero-arm debit')
print('rank-four positive upper:',float(M4hi),'rank-five signed:',m5)
print('low negative lower:',float(neg),'high zero-arm upper:',float(high),
      'complete two-orientation cost:',float(tol))
