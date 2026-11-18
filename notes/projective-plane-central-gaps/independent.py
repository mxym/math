"""Exact independent incidence and unnormalized-gap checks; no external packages."""
from fractions import Fraction as Q
from math import comb

def ck(v, msg):
    if not v: raise RuntimeError(msg)

def plane(q):
    # Affine lines plus points at infinity, over F_7 and F_7[i]/(i^2+1).
    ck(q in (7,49) and 6 not in {a*a%7 for a in range(7)}, 'fields')
    def plus(x,y):
        return ((x+y)%7)+7*((x//7+y//7)%7)
    def times(x,y):
        a,b=x%7,x//7; c,d=y%7,y//7
        return (a*c-b*d)%7+7*((a*d+b*c)%7)
    P=q*q+q+1
    rows=[sum(1<<(q*x+plus(times(m,x),b)) for x in range(q)) | 1<<(q*q+m)
          for m in range(q) for b in range(q)]
    rows.extend(sum(1<<(q*a+y) for y in range(q)) | 1<<(q*q+q) for a in range(q))
    rows.append(((1<<(q+1))-1)<<(q*q))
    ck(len(rows)==P and all(s.bit_count()==q+1 for s in rows),'line degrees')
    ds=[0]*P
    for s in rows:
        while s:
            bit=s&-s; ds[bit.bit_length()-1]+=1;s-=bit
    ck(ds==[q+1]*P,'point degrees')
    cnt=0
    for i,r in enumerate(rows):
        for j in range(i):
            ck((r&rows[j]).bit_count()==1, 'line Gram')
            cnt+=1
    ck(cnt==comb(P,2) and sum(ds)==P*(q+1),'coverage')
    return P,len(rows),sum(ds),cnt

if __name__=='__main__':
    p7=plane(7);p49=plane(49)
    ck(p7==(57,57,456,1596) and p49==(2451,2451,122550,3002475), 'plane totals')
    ck(Q(7,64)>Q(5,49) and pow(7,6,36)==1,'Q1')
    for a,b,e in [(20,50,Q(60,7)),(50,150,Q(25)),(30,150,Q(20)),(2,6,Q(1))]:
        av=Q(2*a*b,a+b);gap=min(abs(x-av) for x in [0,a,b,a+b])
        ck(gap==e,'K_(a,b)')
    print('PASS: independent affine completions over F7 and F49:',p7,p49)
