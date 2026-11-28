
"""Exact source, barrier, collision checks; no numerical sandpile arithmetic."""
from collections import deque

ENDS = {1:"3",2:"1 3",3:"03 12 33",4:"22 13 33",5:"220 113 133 333"}
SMALL = {
  1:["0"],
  2:["3","2","2 1"],
  3:["32","21","21 10","03 23","03 23 12"],
  4:["32","13","02 33","23 32","23 32 21"],
  5:["322","132","021 332","232 321","232 321 210","221 131 331","221 131 331 220"]
}

def graph(w,n):
    return [tuple(a*n+b for a,b in ((r+1,j),(r-1,j),(r,j+1),(r,j-1))
                  if 0<=a<w and 0<=b<n) for r in range(w) for j in range(n)]

def delta(a,graph):
    return [4*v-sum(a[j] for j in graph[i]) for i,v in enumerate(a)]

def stabilize(source,d):
    a=source.copy()
    u=[0]*len(a)
    q=deque(i for i,v in enumerate(a) if v>=4)
    while q:
        i=q.popleft()
        if a[i]<4: continue
        k=a[i]//4
        a[i]-=4*k; u[i]+=k
        for j in d[i]:
            if a[j]<4<=a[j]+k: q.append(j)
            a[j]+=k
    return a,u

def old_formula(d):
    a,_=stabilize([6]*len(d),d)
    return stabilize([6-v for v in a],d)[0]

def burning(a,d):
    left=[len(N) for N in d]
    q=deque(i for i,v in enumerate(a) if v>=left[i])
    marked=set(q)
    while q:
        i=q.popleft()
        for j in d[i]:
            left[j]-=1
            if j not in marked and a[j]>=left[j]:
                q.append(j); marked.add(j)
    return len(marked)==len(d)

def sigma(w,n,ends):
    return [2+r*(w+1-r)*sum(j==e for e in ends)
            for r in range(1,w+1) for j in range(n)]

def side(w):
    M=(w+1)**2//4
    b=0
    while b*(b+3)//2<M-1: b+=1
    n=b+2
    d=graph(w,n)
    base=sigma(w,n,[0])
    sup=[(b-j)*(b-j+1)//2 if j<b else 0
         for r in range(w) for j in range(n)]
    assert all(x-y<=3 for x,y in zip(base,delta(sup,d)))
    a,u=stabilize(base,d)
    assert all(x<=y for x,y in zip(u,sup)) and burning(a,d)
    R=max((j+1 for j in range(n) if any(u[r*n+j]>0 for r in range(w))),default=0)
    f=max(j+1 for j in range(n) if any(a[r*n+j]!=2 for r in range(w)))
    assert f==R+1 and f<=b+1
    E=[tuple(a[r*n+j] for r in range(w)) for j in range(f)]
    return E, u, n

def half_columns(a,w,n,count):
    return " ".join("".join(str(a[r*n+j]) for r in range((w+1)//2))
                    for j in range(count))

def main():
    proven_widths=0
    distinct_boards=0
    for w in range(1,61):
        E,u,n0=side(w)
        f=len(E)
        if w in ENDS:
            assert " ".join("".join(map(str, col[:(w+1)//2])) for col in E)==ENDS[w]
            for n,z in enumerate(SMALL[w],1):
                d=graph(w,n)
                start=sigma(w,n,[0,n-1])
                witness=[r*(w+1-r) for r in range(1,w+1) for j in range(n)]
                assert delta(witness,d)==start
                a=stabilize(start,d)[0]
                assert half_columns(a,w,n,(n+1)//2)==z and a==old_formula(d) and burning(a,d)
                distinct_boards+=1
        if w<=30:
            for n in (2*f,2*f+1,2*f+13):
                d=graph(w,n)
                start=sigma(w,n,[0,n-1])
                a=stabilize(start,d)[0]
                cols=E+[(2,)*w]*(n-2*f)+E[::-1]
                assert a==[col[r] for r in range(w) for col in cols]
                assert burning(a,d) and a==old_formula(d)
                distinct_boards+=1
            # At 2f-1 the sum of the two independent odometers is not stabilizing.
            n=2*f-1
            d=graph(w,n)
            start=sigma(w,n,[0,n-1])
            f0=f-1
            U=[(u[r*n0+j] if j<f0 else 0)
               +(u[r*n0+n-1-j] if n-1-j<f0 else 0)
                 for r in range(w) for j in range(n)]
            assert any(x-y>=4 for x,y in zip(start,delta(U,d)))
        proven_widths+=1
    print("PASS",proven_widths,"exact one-sided widths;",distinct_boards,"complete rectangles")

if __name__=="__main__":
    if not __debug__: raise RuntimeError("run without python -O")
    main()
