"""Direct retained-mask checker for local collision refinement and all-radius obstructions."""
from itertools import product,combinations,accumulate,groupby
from collections import Counter
from math import comb
def ck(v,msg):
    if not v:raise ArithmeticError(msg)
def rows(q,m,d):
    n=m+d;cs=list(combinations(range(n),m))
    hist={y:Counter() for y in product(range(q),repeat=m)}
    for x in product(range(q),repeat=n):
        h=Counter(tuple(x[j] for j in s) for s in cs)
        for y,k in h.items():hist[y][k]+=1
    for row in hist.values():row[0]=q**n-row.total()
    return hist
def pcul(q,m,d):
    rs=rows(q,m,d);vs={};L=comb(m+d,d)*q**d
    for y,h in rs.items():
        E=frozenset((i,j) for j in range(m) for i in range(max(0,j-d),j) if y[i]==y[j])
        cls=tuple(sorted((v,t) for v,t in h.items() if t))
        if E not in vs:vs[E]=cls
        ck(vs[E]==cls,'equal collision patterns')
        ck(sum(a*b for a,b in cls)==L,'total')
    ps={E:list(accumulate(k for k,c in reversed(cls) for _ in range(c))) for E,cls in vs.items()}
    comparables=0
    for E1,v1 in ps.items():
        for E2,v2 in ps.items():
            if E1<=E2:
                ck(all(a<=b for a,b in zip(v1,v2)) and ((v1==v2)==(E1==E2)),'all Lorenz comparisons')
                comparables+=1
    b,s=divmod(m+d,m);T=b**(m-s)*(b+1)**s
    if q>=min(m,d+1):ck(min(v[0] for v in ps.values())==ps[frozenset()][0]==T,'peak spaced')
    if (q,m,d)==(3,3,2):ck(max(rs[(0,1,0)])==4,'peak equality not necessarily spaced')
    return len(rs),comparables
def allr(m,d):
    M=m+d;rs=rows(2,m,d);sup=sum(comb(M,k) for k in range(d+1))
    for y,h in rs.items():
        R=sum(1 for _ in groupby(y))
        ck(h[1]==comb(d+m-R+1,d) and h[0]==2**M-sup,'singleton/support formula')
    A=tuple(i%2 for i in range(m))
    if d>=2:ck(max(rs[A])>=m+1,'alternating peak')
    w=tuple(int(i%(d+1)==d) for i in range(m));cap=comb(2*d*d+3*d,d)
    ck(max(rs[w])<=cap,'bounded peak')
    # For the special word use all hosts directly, checking site-by-site the claimed
    # greedy bracketing and local rank-offset argument independently of the row hist.
    un=0;ok=0
    def find(t,x):
        j=0;a=[]
        for i,z in enumerate(x):
            if j<len(t) and z==t[j]:a.append(i);j+=1
        return a if len(a)==len(t) else []
    for x in product(range(2),repeat=M):
        a=find(w,x)
        if not a:continue
        b=[M-1-t for t in reversed(find(w[::-1],x[::-1]))]
        ub=sum(i!=j for i,j in zip(a,b));un=max(un,ub)
        ck(ub<=d+(2*d+1)*d,'uncertain ranks')
        r1={j:i for i,j in enumerate(a)};r2={j:i for i,j in enumerate(b)}
        diff=[(r1[j]-r2[j]) if j in r1 and j in r2 else None for j in range(M)]
        for k,g in groupby(diff):
            seg=len(list(g))
            if k not in (None,0):ck(abs(k)<=d and seg<=d,'offset segment')
        ok+=1
    ck(ok==sup,'greedy support')
    return len(rs),ok
def main():
    pars=[(q,m,d) for q,lim in [(2,8),(3,6),(4,6)] for m in range(1,lim) for d in range(1,min(lim-m,3)+1)]+[(4,4,3)]
    a=b=0
    for t in pars:
        x,y=pcul(*t);a+=x;b+=y
    print(f'Raw q-ary masks: {len(pars)} parameter triples, {a} output words, {b} including-reflexive collision-class comparisons; all descending prefixes, strictness and applicable peak identities PASS.')
    a=b=0
    for d in range(1,5):
        for m in range(1,9):
            x,y=allr(m,d);a+=x;b+=y
    print(f'Fixed-radius binary direct masks: {a} outputs checked for exact singleton and support formulas and stated peaks; {b} matching periodic-pattern hosts checked for greedy rank-offset localization (1<=d<=4, 1<=m<=8).')
if __name__=='__main__':main()
