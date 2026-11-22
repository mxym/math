"""Exact checks for the long-free branch. Run with python -O or python."""
from fractions import Fraction as F
from itertools import product
from math import comb, gcd, isqrt
from functools import lru_cache

def ck(b, msg):
    if not b:
        raise RuntimeError(msg)

def dec(s): return F(str(s))
xi = F(1,10000)
rho_lo, rho_hi = map(dec, (".6038",".6092"))
v_hi = dec(".389")
cut = dec(".766")
u0 = dec(".24")
n_rails=0
# Set w=cut-v/2+delta. Every required saving is weakly decreasing
# in delta, so the two endpoint v's and rho's at delta=0 suffice.
for rho,v in product((rho_lo,rho_hi),(F(0),v_hi)):
    w = cut-v/2
    ck(2*w>1 and w>=dec(".5715"),"unique free factor")
    ck(1-v>dec(".505"),"old r bound")
    ck(1-v-w<u0,"cofactor below HB cutoff")
    ck(1-v-w>=dec(".0395"),"signed harmonic endpoint")
    ck(rho+v-1+2*xi<=dec("-.0016"),"diagonal relative power")
    ck(F(5,4)*rho-w-v/2+2*xi<=dec("-.0043"),"offdiagonal relative power")
    ck(1-v-2*w+2*xi<=dec("-.531"),"no reciprocal wrap")
    n_rails+=1
ck(5*u0>1,"HB valid through full physical r")
ck(sum((-1)**(j-1)*comb(5,j)*(j-1) for j in range(2,6))==-1,"finite HB coefficient")
ck(dec("1.22")>2-dec(".8") and dec("1.26")<2-dec(".65")*dec("1.1"),"common radial region")
ck(1-dec(".02")-dec(".38")/2>cut,"two opposite true sign labels")
ck(1-v_hi/2>cut,"all low semiprimes")
ck(2*dec(".25")>v_hi and dec(".389")<dec(".505"),"triprime s and proper divisors")

@lru_cache(None)
def divs(n):
    a=[]
    for d in range(1,isqrt(n)+1):
        if n%d==0:
            a.append(d)
            if d*d!=n: a.append(n//d)
    return tuple(a)

@lru_cache(None)
def mu(n):
    t=n
    sign=1
    p=2
    while p*p<=t:
        if t%p==0:
            t//=p
            if t%p==0: return 0
            sign=-sign
        p+=1
    return -sign if t>1 else sign

def mu2(n): return sum(mu(d)*mu(n//d) for d in divs(n))

U=35
@lru_cache(None)
def conv(n,j,h):
    """Original j truncated Möbius and h unrestricted independent factors."""
    if not j and not h: return int(n==1)
    if j: return sum(mu(d)*conv(n//d,j-1,h) for d in divs(n) if d<=U)
    return sum(conv(n//d,0,h-1) for d in divs(n))

n_hb = n_cut = 0
for r in range(1,6500):
    ck(sum((-1)**(j-1)*comb(5,j)*conv(r,j,j-1) for j in range(1,6))==mu(r),"HB identity")
    n_hb+=1
    for extra in (0,3,10):
        T=max(isqrt(r)+1,(r+U-1)//U)+extra
        ck(T*T>r and r<=T*U,"cut assumptions")
        direct=0
        for j in range(2,6):
            for a in divs(r):
                if a>T:
                    direct+=(-1)**(j-1)*comb(5,j)*(j-1)*conv(r//a,j,j-2)
        ck(direct==-sum(mu2(r//a) for a in divs(r) if a>T),"exact long-free opening")
        n_cut+=1

n_gcd = 0
for Q0 in (101,153,307):
  H,C=8,12
  for h,h2,c,c2 in product(range(1,H+1),range(1,H+1),range(1,C+1),range(1,C+1)):
    det=h*c2-h2*c
    for Q in (Q0,Q0+2,2*Q0-1):
      if gcd(3*c*c2,Q)>1: continue
      b=pow(3*c,-1,Q)*h-pow(3*c2,-1,Q)*h2
      ck(gcd(b,Q)==gcd(det,Q),"unit quotient gcd")
      if H*C<Q:
        ck((b%Q==0)==(det==0),"no-wrap complete diagonal")
      n_gcd+=1
print(f"{n_rails} sharp rail endpoints; {n_hb} whole HB, {n_cut} free HB, {n_gcd} inverse-gcd checks passed")
