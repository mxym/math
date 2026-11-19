"""Independent, exact DP checks of the different native-bond mask cases."""
from itertools import combinations

def require(c, why):
    if not c: raise ArithmeticError(why)

def maskout(y,S):
    S=set(S)
    return ''.join(c for i,c in enumerate(y) if i not in S)

def count(y,x):
    counts=[1]+[0]*len(x)
    for a in y:
        for j in range(len(x)-1,-1,-1):
            if x[j]==a:counts[j+1]+=counts[j]
    return counts[-1]

checked=0
for k,b in [(4,2),(4,3),(4,4),(5,3),(6,3),(8,4)]:
    m=5*k+8
    n=b*m+1
    y=''
    for i in range(b):
        first=y[-1] if y else '0'
        other='0' if first=='1' else '1'
        L=m+int(i==0)
        y+=((first+other)*((L+1)//2))[:L]
    A=('01'*n)[:n]
    native=[i for i in range(n-1) if y[i]==y[i+1]]
    regular=[1+3*i for i in range(k)]
    def chk(S, want_y, label):
        global checked
        z=maskout(y,S)
        v=count(y,z)
        w=count(A,maskout(A,S))
        if isinstance(want_y, tuple):
            require(want_y[0]<=v<=want_y[1] and w==n-k+1,(k,b,label,v,w))
        else:
            require(v==want_y and w==1,(k,b,label,v,w))
        checked+=1
    chk(regular,1,'isolated')
    for p in native:
        for q in (p,p+1):chk(regular[:k-1]+[q],2,'one copy')
    cuts=[-1]+native+[n]
    # Pair at the start-half of last segment, away from all anchors.
    first_last=n-m+2
    v=1+((m-1)-2)  # The last segment loses its left native copy from the flank; two selected sites omitted.
    chk(regular[:k-2]+[first_last,first_last+1],(v,v+2*(b-1)),'one adjacent pair')
print('PASS exact DP native-copy, isolated and adjacent-pair comparisons:',checked)
