"""Independent exact verifications from deleted position masks. Standard library only."""
from itertools import combinations,groupby,accumulate,product
from math import comb
from collections import Counter
def ck(x,msg):
    if not x:raise ArithmeticError(msg)
def pred(m):
    if m==1:return 3
    return min(max(4,m+1),max(6,3+(m-1)//2),9)
def wordwise(y):
    m=len(y); runs=[len(list(c)) for k,c in groupby(y)]
    if max(runs)>=3:return None
    inds=[i for i,r in enumerate(runs) if r==2]
    if not inds:return max(3 if m==1 else 4,m+1)
    side=[inds[0],len(runs)-1-inds[-1]]
    return max([6 if len(inds)==1 else 9]+[3+s for s in side]+[5+b-a-1 for a,b in zip(inds,inds[1:])])
def direct(m):
    n=m+2; maxima=[0]*(1<<m)
    masks=[(i,j,(1<<j)-1,(1<<i)-1) for i,j in combinations(range(n),2)]
    for x in range(1<<n):
        hist={}
        for i,j,bj,bi in masks:
            z=((x>>(j+1))<<j)|(x&bj)
            y=((z>>(i+1))<<i)|(z&bi)
            hist[y]=hist.get(y,0)+1
        for y,v in hist.items():
            if v>maxima[y]:maxima[y]=v
    ck(min(maxima)==pred(m),f'minimum {m}')
    for i,v in enumerate(maxima):
        w=format(i,f'0{m}b');u=wordwise(w)
        ck((u==v if u is not None else v>=10),f'peak {m} {w}')
    return len(maxima)
def moment2(y):
    # Overlay all ordered pairs of retained masks; free host positions contribute 2 each.
    m=len(y);n=m+2
    req=[]
    for deleted in combinations(range(n),2):
        active=[j for j in range(n) if j not in deleted]
        mask=sum(1<<j for j in active)
        value=sum((b=='1')<<j for b,j in zip(y,active))
        req.append((mask,value))
    return sum(1<<(n-(a|b).bit_count()) for a,v in req for b,w in req if not ((v^w)&(a&b)))
def patt(m,l):
    r=m-2-l
    return ''.join(str(j%2)*(2 if j==l else 1) for j in range(m-1))
def small_cases():
    count=0
    for m in range(1,6):
        n=m+2
        data={w:[] for w in product("01",repeat=m)}
        masks=list(combinations(range(n),m))
        for x in product("01",repeat=n):
            h=Counter(tuple(x[j] for j in u) for u in masks)
            for w,v in h.items():data[w].append(v)
        pref={w:tuple(accumulate(sorted(h,reverse=True)+[0]*((1<<n)-len(h)))) for w,h in data.items()}
        alt=tuple(str(i%2) for i in range(m))
        ck(all(min(b-a for a,b in zip(pref[alt],v))==0 for v in pref.values()),'least at small m')
        ck(all((v==pref[alt])==all(w[i]!=w[i+1] for i in range(m-1)) for w,v in pref.items()),'least equality')
        count+=len(data)
    print(f'All {count} binary observations of lengths 1..5: every exact Lorenz prefix verifies the alternating least element and strict equality classification.')
def main():
    small_cases()
    total=sum(direct(m) for m in range(1,14))
    print(f'All {total} binary outputs of lengths 1..13: raw n choose 2 deletion masks verify minimax peaks and the stated equality classification.')
    cnt=0
    for m in range(2,29):
        a=''.join(str(i%2) for i in range(m));v=moment2(a)
        for l in sorted({0,(m-2)//2,m-2}):
            r=m-2-l;u=moment2(patt(m,l));ck(u-v==8*m-2*l*r,'collision difference');cnt+=1
        if m==20:print(f'm=20 exact squared multiplicity sums: alternating={v}, central double={moment2(patt(m,9))}.')
    print(f'{cnt} exact collision comparisons by joint-mask counting through length 28: PASS.')
if __name__=='__main__':main()
