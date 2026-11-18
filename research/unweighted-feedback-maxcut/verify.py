"""Exact finite part: the number in table is 15*2^n times the minimum gap."""
from math import comb
def need(x, msg):
    if not x:
        raise ArithmeticError(msg)
def packed(n,m):
    d=[1]*n
    r=2*m-n
    for j in range(n):
        a=min(n-2,r)
        d[j]+=a;r-=a
    need(r==0 and sum(d)==2*m and min(d)>=1 and max(d)<=n-1,(n,m,d))
    return d
def count(d):
    a=[1]
    for x in d:
        b=a+[0]*x
        for j,v in enumerate(a):
            b[j+x]+=v
        a=b
    s=sum(d)
    need(sum(a)==2**len(d) and len(a)==s+1 and a==a[::-1],d)
    return sum(c*abs(2*j-s) for j,c in enumerate(a))
def main():
    cells=0; ties=[]; log=[]
    for n in range(2,17):
        row=[]
        for m in range(n-1,comb(n,2)+1):
            d=packed(n,m)
            L=(2*m+n+2)//4
            gap=(15*L-6*m)*2**n-4*count(d)
            need(gap>=0, (n,m,d,gap))
            if gap==0:ties.append((n,m))
            row.append((gap,m));cells+=1
        log.append((n,len(row),*min(row)))
    need(cells==575 and ties==[(3,3),(5,10)],(cells,ties))
    print('n cells min_integer_gap first_m_for_min')
    for ent in log:print(*ent)
    print(f'{cells} cells; equality in integer test: {ties}. PASS')
if __name__=='__main__':main()
