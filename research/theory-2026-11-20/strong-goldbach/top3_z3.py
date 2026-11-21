"""Column-first capped incidence, rational nullspaces by primitive integer Gauss elimination.
Run with python3 -O. No third-party modules and no assert-dependent checks.
"""
from itertools import product
from math import gcd, prod
from functools import reduce
from hashlib import sha256

def prim(r):
    g=reduce(gcd,r,0)
    return [v//g for v in r] if g else r

def kernel(A,n=6):
    A=[list(r) for r in A]
    piv=[]
    for x in range(n):
        t=len(piv)
        j=next((s for s in range(t,len(A)) if A[s][x]),None)
        if j is None: continue
        A[t],A[j]=A[j],A[t]
        A[t]=prim(A[t])
        for s in range(len(A)):
            if s!=t and A[s][x]:
                a,b=A[t][x],A[s][x]
                A[s]=prim([a*y-b*z for y,z in zip(A[s],A[t])])
        piv.append(x)
    den=prod(abs(A[j][x]) for j,x in enumerate(piv))
    basis=[]
    for z in range(n):
        if z in piv: continue
        v=[0]*n
        v[z]=den
        for j,x in enumerate(piv): v[x]=-A[j][z]*den//A[j][x]
        basis.append(prim(v))
    return basis


from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations
import ast,ctypes as ct,ctypes.util
# The only external dependency of this cross-check is libz3 (QF_LIA).
lib=ct.CDLL(ctypes.util.find_library('z3'))
P,S=ct.c_void_p,ct.c_char_p
def fn(n,out,*args):
    f=getattr(lib,n);f.restype=out;f.argtypes=list(args);return f
config=fn('Z3_mk_config',P)()
ctx=fn('Z3_mk_context',P,P)(config)
evals=fn('Z3_eval_smtlib2_string',S,P,S)
T={"001000011001100010":["k>=2","d0=0","d1=2*k","d2=0","d3=k","d4=0","d5=0"],"001000020001100010":["k>=2","d0=0","d1=2*k","d2=0","d3=k","d4=0","d5=0"],"010000002001100001":["k>=2","d0=0","d1=2*k","d2=0","d3=k","d4=0","d5=0"],"001100000000000020":["k>=4","d0=0","d1=k","d2=0","3*d3=1+2*k","d4=k","d5=0"],"100001000000000020":["k>=4","d0=0","d1=k","d2=k","3*d3=1+2*k","d4=0","d5=0"],"010002000001000100":["k>=3","d0>=0","2*d0<=k-1","d1=0","2*d2=1+3*k","d3=k-d0","d4=k","d5=0"],"010002010001000100":["k>=3","d0=0","d1=0","2*d2=1+k","d3=k","d4=k","d5=0"],"020100000001000002":["k>=4","d0=0","d1=k","d2=0","3*d3=k-1","3*d4=1+2*k","d5=0"],"020100010000000001":["k>=3","d0=0","d1=k","d2=0","d3=k","2*d4=1+3*k","d5=0"],"100020000001000002":["k>=4","3*d0>=k+2","d0<=k","d1=0","d2=k-d0","3*d3=k-1","3*d4=1+2*k","d5=0"],"100020010000000001":["k>=3","4*d0>=3*k+3","d0<=k","d1=0","d2=k-d0","d3=k","2*d4=1+3*k","d5=0"]}
names=['d'+str(i) for i in range(6)]
def plus(X):
    r=list(X)
    return '0' if not r else r[0] if len(r)==1 else '(+ '+' '.join(r)+')'
def A(op,*a):return '('+op+' '+' '.join(map(str,a))+')'
def lin(v):return plus(A('*',x,n) for x,n in zip(v,names) if x)
def dot(a,b):return sum(x*y for x,y in zip(a,b))
def cross(x,y):return [x[1]*y[2]-x[2]*y[1],x[2]*y[0]-x[0]*y[2],x[0]*y[1]-x[1]*y[0]]
def compiled(s):
    op={ast.Add:'+',ast.Mult:'*',ast.Sub:'-',ast.Eq:'=',ast.GtE:'>=',ast.LtE:'<='}
    def get(x):
        if isinstance(x,ast.Name):return x.id
        if isinstance(x,ast.Constant):return str(x.value)
        if isinstance(x,ast.Compare):return A(op[type(x.ops[0])],get(x.left),get(x.comparators[0]))
        return A(op[type(x.op)],get(x.left),get(x.right))
    return get(ast.parse(s.replace('>=','#').replace('<=','!').replace('=','==').replace('#','>=').replace('!','<='),mode='eval').body)
def OR(L):return 'false' if not L else L[0] if len(L)==1 else A('or',*L)
def AND(L):return 'true' if not L else L[0] if len(L)==1 else A('and',*L)
def primitive_fraction(v,q):
    g=reduce(gcd,list(v)+[q],0)
    if q<0:g=-g
    return [x//g for x in v],q//g

# Column-first generation, independent rational-kernel method, no global cuts required.
opts=[]
for j in range(2,5):
    opts.append([c for c in product(range(3),repeat=6) if not c[j] and
                 sum(bool(c[i]) for i in range(6) if i<2 or i>j)<=1])
raw=ns=0
def run(cols,cap):
    global raw,ns
    if len(cols)<3:
        for c in opts[len(cols)]:
            if all(x<=y for x,y in zip(c,cap)):
                run(cols+[c],[y-x for x,y in zip(c,cap)])
        return
    raw+=1
    r=tuple(zip(*cols));tag=''.join(str(x) for row in r for x in row)
    if cap[0]==2 and cap[1]:return
    FF=[[e-(i==j+2) for i,e in enumerate(col)] for j,col in enumerate(cols)]
    H=kernel(FF)
    if len(H)!=3:return
    ga=list(zip(*H))
    E=ga[5];V=[dot(h,[2,2,1,1,1,2]) for h in H]
    if not any(E):return
    normal=cross(V,E)
    if not any(normal):
        ks=[F(e,v) for v,e in zip(V,E) if v]
        if ks and ks[0]>1 and all(ks[0]*v==e for v,e in zip(V,E)):
            raise RuntimeError('dependent pencil at '+str(ks[0]))
        return
    # On C, the oriented determinants of Gale pairs are proportional to
    # these scalar triples with common normal k*V-E.
    negE=[-x for x in E]
    lines=[[ (dot(V,cross(x,y)),dot(negE,cross(x,y))) for y in ga] for x in ga]
    cuts=sorted({F(1)} | {F(-b,a) for row in lines for a,b in row if a and F(-b,a)>1})
    def admiss(k):
        D=[[a*k+b for a,b in row] for row in lines]
        return D[0][1] and all(sum(t>0 for t in row)>=2 and sum(t<0 for t in row)>=2 for row in D)
    valid=[]
    for i,lo in enumerate(cuts):
        hi=cuts[i+1] if i+1<len(cuts) else None
        if lo>1 and admiss(lo):valid.append((lo,lo))
        if admiss((hi+lo)/2 if hi else lo+1):valid.append((lo,hi))
    if not valid:return
    J=prim([dot(normal,g) for g in ga])
    choices=[]
    for i,j in combinations(range(3),2):
        det=V[i]*E[j]-V[j]*E[i]
        if not det:continue
        X=[g[i]*E[j]-g[j]*E[i] for g in ga];Y=[V[i]*g[j]-V[j]*g[i] for g in ga]
        psi,pv=primitive_fraction(X,det);phi,pe=primitive_fraction(Y,det)
        lo=hi=psi[1]*cap[1]
        for w in (0,2,3,4):
            if w==0 and cap[1]:continue
            lo+=min(0,psi[w]*cap[w]);hi+=max(0,psi[w]*cap[w])
        Tlo=-((-pe*(pv-hi))//pv);Thi=(pe*(pv-lo))//pv
        choices.append((Thi-Tlo,Tlo,Thi,psi,pv,phi,pe))
    _,Tlo,Thi,psi,pv,phi,pe=min(choices)
    for i,j in combinations(range(6),2):
        if sum(min(x,y) for x,y in zip(r[i],r[j]))>=2:return
    core=[A('=',lin(J),0),A('=','d5',0)]
    if cap[1]:core.append(A('=','d0',0))
    if cap[0]==2:core.append(A('>','d0',0))
    # Get the left-null row as a linear function of d, independently by
    # signed minors of [Z,1,d] expanded on the last column.
    cols4=cols+[(1,)*6]
    def d4(indices):
        m=[[c[i] for c in cols4] for i in indices]
        # Bareiss-free Leibniz determinant; entries are small.
        return sum(sgn*prod(rr[t] for rr,t in zip(m,perm)) for perm,sgn in perms4)
    L=[]
    for i in range(6):
        keep=[a for a in range(6) if a!=i];v=[0]*6
        for j,x in enumerate(keep):v[x]=(-1)**(i+j)*d4([a for a in keep if a!=x])
        L.append(v)
    pf=[];w=[0]*6
    for i in [2,3,4,5,1]:
        w=[a+b for a,b in zip(w,L[i])];pf.append(lin(w))
    core += [A('distinct',pf[0],0),OR([A('<',x,0) for x in pf]),OR([A('>',x,0) for x in pf]),
             OR([A('<',pf[0],0),A('<',pf[1],0),A('<=',pf[2],0)]),
             OR([A('>',pf[0],0),A('>',pf[1],0),A('>=',pf[2],0)])]
    for i,j in combinations(range(6),2):
        if r[i]==r[j]:core.append(A('distinct',names[i],names[j]))
        if any(x*y for x,y in zip(r[i],r[j])):core.append(OR([A('=',names[i],0),A('=',names[j],0)]))
    for t in range(Tlo,Thi+1):
        if t==pe:continue
        ratio=F(pe,pv*(pe-t));P0,Q=ratio.numerator,ratio.denominator
        v=core+[A('=',lin(phi),t),A('=','j',A('*',P0,lin(psi))), A('=',A('*',Q,'d1'),A('*',cap[1],'j'))]
        def bound(a,op):return A(op,A('*',a.denominator,'j'),a.numerator*Q)
        rails=[]
        for lo,hi in valid:
            rails.append(bound(lo,'=') if lo==hi else AND([bound(lo,'>')]+([bound(hi,'<')] if hi is not None else [])))
        v.append(OR(rails))
        for name,c in zip(names,cap):v += [A('>=',name,0),A('<=',A('*',Q,name),A('*',c,'j'))]
        for i,jj in combinations(range(6),2):
            if not any(x*y for x,y in zip(r[i],r[jj])):v.append(OR([A('<=',A('*',Q,names[x]),'j') for x in (i,jj)]))
        if tag in T:
            ok=AND([A('=',A('mod','j',Q),0)]+[compiled(eq) for eq in T[tag]])
            v.append(A('not',ok))
        inp='(reset) (set-logic QF_LIA)\n'+' '.join('(declare-const '+nm+' Int)' for nm in ['j']+names)
        inp+=' (define-fun k () Int (div j '+str(Q)+')) (assert '+AND(v)+') (check-sat)'
        verdict=evals(ctx,inp.encode()).decode().strip()
        if verdict!='unsat':raise RuntimeError((tag,t,Q,verdict))
        ns+=1

from itertools import permutations
perms4=[(p,(-1)**sum(p[i]>p[j] for i in range(4) for j in range(i+1,4))) for p in permutations(range(4))]
run([], [2]*6)
print('column-first top charts',raw,'independent QF_LIA noncoverage checks UNSAT',ns)
if raw!=7290 or ns!=891:raise SystemExit('coverage failure')
