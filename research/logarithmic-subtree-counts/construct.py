"""Exact digit constructor for the large-k theorem; Python 3 standard library."""
from hashlib import sha256

M0 = 46783
B = tuple(34 + 288*d for d in range(18))
def base(d):
    s,u = 17*d,17-d
    p=s+u+1
    return 40+p*(p+1)//2+16*(s+1)*(u+1)
H = tuple(map(base,range(18)))

def W(j,p,d):
    return H[d]+306*((p-1)//16)*B[d]

def extremum(j,p,d):
    """Sum of weights in the j least significant places, p=17**j."""
    return j*H[d]+306*B[d]*(((p-1)//16-j)//16)

def construct(k):
    """Return list of (digit,epsilon) in chronological order. No huge graph materialization."""
    if k < extremum(M0,17**M0,0): raise ValueError("below the theorem's explicit threshold")
    lo,hi=M0,k.bit_length()+1
    while lo+1<hi:
        m=(lo+hi)//2
        if extremum(m,17**m,0)<=k:lo=m
        else:hi=m
    m=lo
    p=17**m
    if k>extremum(m,p,17)+m: raise ArithmeticError("length coverage")
    digits=[]
    for j in range(m-1,-1,-1):
        p//=17
        low=extremum(j,p,0);high=extremum(j,p,17)+m
        # The smallest digit with a high endpoint >= remaining k.
        le,ri=0,17
        while le<ri:
            c=(le+ri)//2
            if W(j,p,c)+high<k:le=c+1
            else:ri=c
        val=W(j,p,le)
        if not low<=k-val<=high:raise ArithmeticError("prefix hole")
        k-=val
        digits.append(le)
    if not 0<=k<=m:raise ArithmeticError("terminal slack")
    return [(d,int(i<k)) for i,d in enumerate(digits)]

def replay(word):
    f=t=n=0
    for d,e in word:
        t+=306*f+H[d]+e
        f=17*f+B[d]
        n+=18+16*d+7+e
    return f,t,n

def check(b,msg):
    if not b:raise ArithmeticError(msg)

if __name__=='__main__':
    # Intentionally not asserting the theorem by sampling: full carry bounds are in PROOF.md.
    p=17**M0;lo=extremum(M0,p,0);hi=extremum(M0,p,17)+M0
    k=(lo*3+extremum(M0+1,17*p,0)*4)//7+12345
    word=construct(k)
    f,t,n=replay(word)
    check(t==k and len(word)==M0 and n<=298*M0 and k>=p,'large inverse witness')
    print('PASS exact inverse witness at first covered length:',len(word),'digits;',k.bit_length(),'target bits;',n,'vertices')
    print('digit/switch bytes SHA-256:',sha256(bytes(2*d+e for d,e in word)).hexdigest())
    print('target big-endian bytes SHA-256:',sha256(k.to_bytes((k.bit_length()+7)//8,'big')).hexdigest())
