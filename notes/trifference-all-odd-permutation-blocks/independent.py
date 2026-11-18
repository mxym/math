"""Independent conditioned-first-word and cycle-coloring certificates; no project imports."""
from fractions import Fraction as Q
from math import factorial as fac, comb, prod
from decimal import Decimal as Dec, localcontext
from itertools import product,combinations

def must(v,msg):
    if not v: raise ValueError(msg)

def comp4(q):
    for a in range(q+1):
       for b in range(q-a+1):
          for c in range(q-a-b+1):
             yield (a,b,c,q-a-b-c)

def parity_f(q):
    n=q+2; size=comb(n,3)*fac(q)
    # Fix x=(0,0,0,1,...,q-1). Use only 2q signs for y,z.
    ts=list(product((1,-1),repeat=2))
    num=0
    for c in comp4(q-1): # types of the q-1 singly occurring letters
        multi=fac(q-1)//prod(map(fac,c))
        for typ in range(4): # the repeated symbol
            m=list(c);m[typ]+=1
            a=sum(m[i]*ts[i][0] for i in range(4))
            b=sum(m[i]*ts[i][1] for i in range(4))
            w=sum(m[i]*ts[i][0]*ts[i][1] for i in range(4))
            L=[x*b+y*a+w-2*x*y for x,y in ts]
            sign=prod((x*y)**k for (x,y),k in zip(ts,m))
            num+=multi*sign*prod(z**k for z,k in zip(L,m))*L[typ]**2
    count, rem=divmod(num,4**q)
    must(rem==0 and 0<count<size**2,("conditional count",q,count,rem))
    return size,size*count,Q(count,size**2)

def perm_counts(k):
    # m is the number of moved symbols of sigma. g[m] counts derangements
    # with one of two colors chosen independently for each cycle.
    g=[1,0]
    for m in range(2,k+1):g.append((m-1)*(g[-1]+2*g[-2]))
    h=Q(0)
    for q in range(k+1):
        h+=Q(g[q],fac(q))
        pairs=h*fac(q)
        must(pairs.denominator==1,("permutation divisibility",q))
        yield q,Q(pairs,fac(q)**2)

def pass_gap(q,n,f):
    r=f/Q(3*q-2,q*q)**n
    must(0<f<1 and (r.denominator**350)>(r.numerator**350 << (2*n)),("gap",q,n))
    return r

def showrate(f,div):
    with localcontext() as ctx:
        ctx.prec=55
        return (Dec(f.denominator)/Dec(f.numerator)).ln()/Dec(2).ln()/div

if __name__=="__main__":
    for q in range(3,20):
        s,d,f=parity_f(q)
        if q>=4: r=pass_gap(q,q+2,f)
        if q==9:
            must((s,d)==(59875200,458769821652172800),"advertised count")
            must(f==Q(5441833,2546192880000),"exact fraction")
            must(f.numerator**25000*(2**(88*5351)) < f.denominator**25000,"rate threshold")
            y=(Q(25,81)**14)*(1-4*Q(7,9)**14+3*Q(161,225)**14)/(1-Q(7,9)**14)**3
            must(y**11>f**14,"old comparison")
            print("ternary:",showrate(f,88),"vs",showrate(y,112))
        print("odd block",q,s,d)
    for q,f in perm_counts(255):
        if q>=20:pass_gap(q,q,f)
    # independent direct tiny case, avoiding both parity masks and parity-state DP
    q=3; n=q+2; x=[0]*3+list(range(1,q))
    words=[w for w in product(range(q),repeat=n) if all(w.count(i)%2==1 for i in range(q))]
    d=sum(all(len({a,b,c})<=2 for a,b,c in zip(x,y,z)) for y in words for z in words)*len(words)
    must(d==parity_f(q)[1],"tiny raw word triples")
    must(Q(3*256-2,256)>Q(11,4)*Q(17,16) and 17**12>2*16**12 and 258**30<2**256,"tail")
    # e <= 1+1+1/2 + (1/6)/(1-1/4) < 11/4.
    must(Q(5,2)+Q(1,6)/(1-Q(1,4))<Q(11,4),"e upper")
    tetra=[(a,b,(a+b)%3,(a+2*b)%3) for a,b in product(range(3),repeat=2)]
    must(all(any(len(set(t))==3 for t in zip(*T)) for T in combinations(tetra,3)),"84 Tetra triples")
    print("PASS: 16 all-odd alphabets, 236 permutation alphabets, 84 tetra triples and analytic endpoint guards")
