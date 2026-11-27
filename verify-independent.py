# Independent exact recomputation, not importing the authors' code.
from fractions import Fraction as R
from functools import lru_cache
from itertools import combinations, combinations_with_replacement, product
from math import gcd, isqrt, factorial
import hashlib

S=10**7

def alternating_atan(n):
    v=sum((R((-1)**i,(2*i+1)*n**(2*i+1)) for i in range(28)),R(0))
    return v,v+R(1,57*n**57)

v,w=alternating_atan(5)
a,b=alternating_atan(239)
pi0,pi1=16*v-4*b,16*w-4*a
assert R(31415926,10**7)<pi0<pi1<R(31415927,10**7)

@lru_cache(None)
def half_table(m):
    out=[S]
    for j in range(1,m//2+1):
        if 2*j==m:
            out.append(-S); continue
        z=2*pi0*j/m
        y=z*z
        term=R(1); c=R(1)
        for k in range(1,22):
            term *= -y/(2*k*(2*k-1))
            c+=term
        # Taylor through degree 43 (the odd coefficient is zero).
        lower=c-z**44/factorial(44)-2*(pi1-pi0)*j/m
        out.append(S*lower//1)
    return out

def coslo(m,j):
    j%=m
    return half_table(m)[min(j,m-j)]

def canon(m,K):
    return min(tuple(sorted(min(z%m,(-z)%m) for z in [u*k for k in K]))
               for u in range(1,m) if gcd(m,u)==1)

def reps(m,r):
    return sorted({canon(m,(1,)+K) for K in combinations(range(2,m//2+1),r-1)})

def cut(convex,ineq):
    if not convex: return []
    a,b,c=ineq
    def height(P): return a*P[0]+b*P[1]+c*P[2]
    out=[]
    prev=convex[-1]; u=height(prev)
    for cur in convex:
        v=height(cur)
        if (u<0<v) or (v<0<u):
            neg,pos=(prev,cur) if u<0 else (cur,prev)
            un,up=(u,v) if u<0 else (v,u)
            hit=tuple(up*x-un*y for x,y in zip(neg,pos))
            div=gcd(*hit)
            out.append(tuple(x//div for x in hit))
        if v<=0: out.append(cur)
        prev,u=cur,v
    return list(dict.fromkeys(out))

def poly(m,A):
    p=[(0,0,1),(1,0,1),(0,1,1)]
    for z in A:
        if not any(z):continue
        a,b,c=(coslo(m,i) for i in z)
        p=cut(p,(2*(a-c),2*(b-c),2*c-S))
        if not p:return []
    return p

def group_cyclic(m,K):
    return [tuple(j*k%m for k in K) for j in range(m)]

def count_primes():
    checks=0
    census={}
    for q in range(7,133):
        if any(q%i==0 for i in range(2,1+isqrt(q))):continue
        r=1 if q<=13 else (2 if q<=41 else 3)
        for K in reps(q,r):
            assert not poly(q,group_cyclic(q,K+(K[-1],)*(3-r))), (q,K)
            checks+=1
        census[q]=r+1
    print("independent prime polygons checked:",checks,flush=True)
    return census

def component(P,j):
    return P[j] if j<2 else P[2]-P[0]-P[1]

def split(P):
    ends=[]
    for i in range(3):
        a=[R(component(v,i),v[2]) for v in P]
        ends.append((max(a)-min(a),(min(a)+max(a))/2))
    j=max(range(3),key=lambda x:ends[x][0])
    z=ends[j][1]; n,d=z.numerator,z.denominator
    row=[(d,0,-n),(0,d,-n),(-d,-d,d-n)][j]
    a,b=cut(P,row),cut(P,tuple(-v for v in row))
    assert a and b
    return a,b

def endpoints(P,R1):
    res=[]
    for x,y in product(P,R1):
        X,Y=x[2],y[2]
        ls=[]; us=[]
        for i in range(3):
            xi,yi=component(x,i),component(y,i)
            assert xi>=0 and yi>=0
            ls.append(isqrt((S*S*xi*yi)//(X*Y)))
            us.append(-(-(S*(xi*Y+yi*X))//(2*X*Y)))
        res.append((ls,us))
    return res

def exclusion(m,A,d,P,R1):
    # New direct Taylor interval table, unlike the original iterated rotation.
    N=m*64
    sh=[tuple(j*64 for j in v) for v in A]
    prs=endpoints(P,R1)
    boxes=[tuple((0,N//e) for e in d)]
    count=0

    @lru_cache(None)
    def phase_col(i,l,r):
        return tuple(-S if (N//2-l-g[i])%N <= r-l else
                     min(coslo(N,l+g[i]),coslo(N,r+g[i])) for g in sh)

    while boxes:
        I=boxes.pop(); count+=1
        all_rows=zip(*(phase_col(j,l,r) for j,(l,r) in enumerate(I)))
        if any(all(sum(c*(L[j] if c>=0 else U[j]) for j,c in enumerate(row))*2>S*S
                   for L,U in prs) for row in all_rows):
            continue
        z=max(range(3), key=lambda j:I[j][1]-I[j][0])
        l,r=I[z]
        if r-l<=1:return False,count
        mid=(r+l)//2
        I1,I2=list(I),list(I)
        I1[z],I2[z]=(l,mid),(mid,r)
        boxes.append(tuple(I2)); boxes.append(tuple(I1))
    return True,count

def group_orbits():
    counts={}; boxes=0; cells_depth={}
    for m in [37,25]:
        actions=[('C',K,m,group_cyclic(m,K),(m,1,1)) for K in reps(m,3)]
        if m==25:
            sub=[]
            # Enumerate all projective row orbits from scratch.
            for nz in (2,3):
                for b2 in range(nz//2+1):
                    row=(0,)*(3-nz)+(1,)*(nz-b2)+(2,)*b2
                    sub.append(row)
            assert sorted(sub)==[(0,1,1),(0,1,2),(1,1,1),(1,1,2)]
            for H in sub:
                A=[x for x in product(range(5),repeat=3) if sum(h*i for h,i in zip(H,x))%5==0]
                actions.append(('F',H,5,A,(5,5,1)))
        for lab,K,p,A,d in actions:
            P=poly(p,A)
            if not P:continue
            typ=(m,lab); counts[typ]=counts.get(typ,0)+1
            cs=[P]
            for level in range(5):
                residual=set()
                for i,j in combinations_with_replacement(range(len(cs)),2):
                    ok,q=exclusion(p,A,d,cs[i],cs[j]); boxes+=q
                    if not ok:residual.add((i,j))
                if not residual or (m==25 and not any({(i,j),(i,k),(j,k)}<=residual
                    for i,j,k in combinations_with_replacement(range(len(cs)),3))):
                    cells_depth[typ]=max(cells_depth.get(typ,0),level);break
                cs=[Q for P in cs for Q in split(P)]
            else:
                raise AssertionError((typ,K))
    assert counts=={(37,'C'):6,(25,'C'):13,(25,'F'):1}
    print("independent continuous certificates:",counts,boxes,cells_depth,flush=True)

def group_census(census):
    for n,ra in [(6,range(73,77)),(7,range(127,133))]:
        for N in ra:
            pset={2,3,5}
            for p,k in census.items():
                dim=n-2*k
                if dim>=0 and N%p<=[0,2,6,12][dim]:
                    pset.add(p)
            if (n,N)==(6,74):pset.remove(37)
            expected=(set([2,3,5,7,11,13]) if n==7 else
                      ({2,3,5,7,19} if N==76 else {2,3,5,7}))
            assert pset==expected

def e6():
    V=[]
    for i,j in combinations(range(5),2):
        for a,b in product([-2,2],repeat=2):
            v=[0]*8;v[i]=a;v[j]=b;V.append(tuple(v))
    for W in product([-1,1],repeat=6):
        v=W[:5]+(W[5],)*3
        if v.count(-1)%2==0:V.append(v)
    assert len(set(V))==72
    dot=lambda v,w:sum(a*b for a,b in zip(v,w))
    assert all(dot(v,v)==8 for v in V)
    assert max(dot(v,w) for v,w in combinations(V,2))==4
    # Norm-squared-eight roots; each reflection v -> v - <v,a>a/4.
    S=set(V)
    for a in V:
        for v in V:
            d=dot(v,a)
            assert d%4==0
            assert tuple(x-d*y//4 for x,y in zip(v,a)) in S
    conn={V[0]};front=[V[0]]
    while front:
        v=front.pop()
        for a in V:
            w=tuple(x-dot(v,a)*y//4 for x,y in zip(v,a))
            if w not in conn:
                conn.add(w);front.append(w)
    assert conn==S
    print("independent E6 witness and reflection transitivity:",len(conn),flush=True)

if __name__=="__main__":
    group_census(count_primes())
    group_orbits()
    e6()
