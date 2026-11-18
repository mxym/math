"""Exact SOS verifier (Python >=3.8 stdlib). No SDP solver, NumPy or floating arithmetic."""
from collections import defaultdict
from fractions import Fraction as Q
from itertools import permutations
from pathlib import Path
import json
DB = Path(__file__).with_name('certificate.json')
def require(b, msg):
    if not b: raise ArithmeticError(msg)
def mulword(u,v):
    # All cross-party generators commute; no same-party commutation. Each generator squares to 1.
    ans=[]
    for side1,side2 in zip(u,v):
        t=[]
        for a in side1+side2:
            if t and t[-1]==a: t.pop()
            else: t.append(a)
        ans.append(tuple(t))
    return tuple(ans)
def inv(w):
    return tuple(t[::-1] for t in w)
def psd(g):
    # Each step is a congruence to a pivot plus a Schur complement.
    pivots=[]
    while g:
        p=g[0][0];require(p>0,'nonpositive exact pivot')
        pivots.append(p)
        g=[[g[i][j]-g[i][0]*g[0][j]/p for j in range(1,len(g))] for i in range(1,len(g))]
    return pivots
def check_equality_forms(forms):
    # Reflections act as transpositions on the plane sum x_i=0, in a rational (nonorthonormal) basis.
    # B_i^T is (A_i-A_(i+1))/sqrt(3) in the real trine Euclidean representation.
    # Acting on vec(I), the Bob word therefore acts on the right in reversed order; its scaling cancels.
    def matmul(a,b):
        return [[sum(a[i][k]*b[k][j] for k in range(2)) for j in range(2)] for i in range(2)]
    def sub(a,b):return [[a[i][j]-b[i][j] for j in range(2)] for i in range(2)]
    eye=[[1,0],[0,1]];A=[]
    for i in range(3):
        t=list(range(3));j=(i+1)%3;t[i],t[j]=t[j],t[i]
        A.append([[int(t[col]==row)-int(t[2]==row) for col in (0,1)] for row in (0,1)])
    D=[sub(A[i],A[(i+1)%3]) for i in range(3)]
    for f in forms:
        z=[[Q(0),Q(0)],[Q(0),Q(0)]]
        for aw,bw,coef in f:
            m=eye
            for i in aw:m=matmul(m,A[i])
            for i in bw[::-1]:m=matmul(m,D[i])
            for i in range(2):
                for j in range(2):z[i][j]+=Q(coef)*m[i][j]
        require(z==[[0,0],[0,0]],'form does not vanish on trine realization')
    print('All 24 unaveraged forms also annihilate the ideal maximally entangled trine vector.')
def check():
    a=json.loads(DB.read_text());forms=a['forms'];n=len(forms)
    require(n==24 and [len(row) for row in a['gram']]==list(range(n,0,-1)),'size')
    g=[[Q(0) for j in range(n)] for i in range(n)]
    for i,row in enumerate(a['gram']):
        for j,value in enumerate(row,i):g[j][i]=g[i][j]=Q(value)
    p=psd([[x-Q(i==j,10**6) for j,x in enumerate(row)] for i,row in enumerate(g)])
    # coefficients are pairs of rationals (a,b), meaning a+b sqrt(3);
    # the inner terms below carry the indicated nonnegative exponent of sqrt(3).
    acc=defaultdict(lambda:[Q(0),Q(0)])
    for perm in permutations(range(3)):
        orientation=1 if (perm[1]-perm[0])%3==1 else -1
        ff=[]
        for form in forms:
            f=[]
            for aw,bw,coef in form:
                require(all(i in (0,1,2) for i in aw+bw),'unknown generator')
                # Under the permutation, edge i→i+1 may have reversed orientation.
                word=(tuple(perm[i] for i in aw),tuple(perm[i] if orientation==1 else perm[(i+1)%3] for i in bw))
                f.append((Q(coef)*orientation**len(bw),len(bw),word))
            ff.append(f)
        for i,x in enumerate(ff):
            for j,y in enumerate(ff):
                common=g[i][j]/6
                for c,e,w in x:
                    for d,f,v in y:
                        power=e+f
                        acc[mulword(inv(w),v)][power%2] += common*c*d*3**(power//2)
    val={w:tuple(c) for w,c in acc.items() if any(c)}
    ideal={((),()):(Q(9),Q(0))}
    for i in range(3):
        ideal[((i,),())]=(Q(3,4),Q(0))
        ideal[((i,),(i,))]=(Q(0),-Q(1))
        ideal[(((i+1)%3,),(i,))]=(Q(0),Q(1))
    require(val==ideal, 'free word identity failed')
    check_equality_forms(forms)
    print('Gram shape 24x24; all',len(p),'exact Schur pivots of G-I/1000000 are positive.')
    print('Exact S3-averaged noncommutative SOS expansion:',len(acc),'distinct reduced words examined;',len(val),'nonzero.')
    print('Target: 9 I - sqrt(3) sum_i (A_i-A_(i+1))B_i + (3/4) sum_i A_i. PASS.')
if __name__=='__main__':check()
