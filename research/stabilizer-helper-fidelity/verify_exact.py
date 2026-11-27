"""Exact modular-label verification; no matrices over complex numbers."""
from itertools import product

def add(u, v, p):
    return tuple((a+b) % p for a,b in zip(u,v))

def scale(t, u, p):
    return tuple(t*a % p for a in u)

def lin(c, rows, p):
    return tuple(sum(a*b for a,b in zip(c, col)) % p for col in zip(*rows))

def dot(u, v, p):
    return sum(u[i+1]*v[i]-u[i]*v[i+1] for i in range(0,len(u),2)) % p

def rank(rows, p):
    if not rows: return 0
    a = [list(v) for v in rows]
    k = 0
    for j in range(len(a[0])):
        i = next((i for i in range(k,len(a)) if a[i][j]), None)
        if i is None: continue
        a[i],a[k]=a[k],a[i]
        a[k]=[x*pow(a[k][j],-1,p) % p for x in a[k]]
        for i in range(k+1,len(a)):
            a[i]=[(x-a[i][j]*y) % p for x,y in zip(a[i],a[k])]
        k+=1
    return k

def weak_test(S, logical, p):
    return (all(dot(a,b,p)==0 for a in S for b in S+logical)
            and rank(S+logical,p)==len(S)+len(logical))

def source():
    labels={'I':(0,0),'X':(1,0),'Z':(0,1),'W':(1,1),
            'Xz':(1,2),'xz':(2,2),'xZ':(2,1),'x':(2,0),'z':(0,2)}
    def row(s):
        return sum((labels[x] for x in s.split()),())
    def sub(v, sites):
        return tuple(v[j] for i in sites for j in (2*i,2*i+1))
    S=list(map(row,["Z Z X X I","Xz xz I X Z","X X W W I","Z Xz I W Z"]))
    ell=list(map(row,["I I xz W X","I I Xz xZ W"]))
    defects=dot(S[1],S[3],3),*(dot(S[3],u,3) for u in ell)
    assert defects==(2,1,2) and not weak_test(S,ell,3)
    repairs=[]
    for i in range(5):
        for a in product(range(3),repeat=2):
            if a==S[-1][2*i:2*i+2]: continue
            candidate=S[-1][:2*i]+a+S[-1][2*i+2:]
            if weak_test(S[:3]+[candidate],ell,3): repairs.append((i,a,candidate))
    assert len(repairs)==1 and repairs[0][:2]==(4,(1,0))
    S[-1]=repairs[0][2]
    assert dot(*ell,3)==1
    A={lin(c,S,3) for c in product(range(3),repeat=4)}
    N={lin(c,S+ell,3) for c in product(range(3),repeat=6)}
    assert (len(A),len(N))==(81,729)
    distance=min(sum(v[i:i+2]!=(0,0) for i in range(0,10,2)) for v in N-A)
    assert distance==3
    assert not any(not any(s[4:]) for s in A if any(s))
    target_pairs=[[(2,2),(1,2)],[(1,1),(2,1)],[(2,0),(2,2)]]
    source_spans=[list(map(row,["Xz xz","Z Xz"])),list(map(row,["xz Xz","Xz Z"]))]
    for i in range(3):
        target=i+2
        rest=[j for j in range(2,5) if j!=target]
        cleaned=[]
        for u in ell:
            solutions=[v for s in A if not any(sub(v:=add(u,s,3),rest))]
            assert len(solutions)==1
            cleaned.extend(solutions)
        b=[sub(v,[target]) for v in cleaned]
        assert b==target_pairs[i]
        defect=(dot(*b,3)-1) % 3
        assert defect==(i==2)
        a=[sub(v,[0,1]) for v in cleaned]
        assert dot(*a,3)==-defect % 3
        if i<2:
            assert rank(a,3)==rank(source_spans[i],3)==rank(a+source_spans[i],3)==2
        print("qutrit target B%d: labels %s, %s; defect rank %d; optimum %s" %
              (i+1,*b,2*(i==2),'1/3' if i==2 else '1'))
    print("printed table negatives (2, 1, 2); all 40 changes checked; unique repair at site 5 Z -> X")
    print("corrected table: 81 stabilizer labels, 729 centralizer labels, logical distance 3")

def realization(p,m,images):
    n=2*m
    V=[tuple(int(i==j) for i in range(n)) for j in range(n)]
    def b(v): return lin(v,images,p)
    def form(v,w): return (dot(b(v),b(w),p)-dot(v,w,p)) % p
    assert rank(images,p)==n
    left=V.copy()
    hp=[]
    while pair:=next(((x,y) for x in left for y in left if form(x,y)),None):
        u,v=pair
        w=scale(pow(form(u,v),-1,p),v,p)
        hp.append((u,w))
        left=[add(add(t,scale(-form(t,w),u,p),p),scale(form(t,u),w,p),p)
              for t in left if t!=u and t!=v]
    r=len(hp)
    q=n-r
    basis=sum((list(uv) for uv in hp),[])+left
    helper_rows=[tuple(int(i==j) for i in range(2*q)) for j in range(n)]
    assert rank(basis,p)==n and len(left)==n-2*r
    # The helper radical uses separate X axes, one per remaining site.
    helper_rows[2*r:]=[tuple(int(i==2*j) for i in range(2*q)) for j in range(r,q)]
    assert len(helper_rows)==n and rank(helper_rows,p)==n
    assert all((dot(helper_rows[i],helper_rows[j],p)+form(basis[i],basis[j])) % p==0
               for i in range(n) for j in range(n))
    ref=lambda v:tuple(x if i%2==0 else -x % p for i,x in enumerate(v))
    J=[ref(v)+a+b(v) for v,a in zip(basis,helper_rows)]
    assert rank(J,p)==n and all(dot(u,v,p)==0 for u in J for v in J)
    K=[u for u,v in hp]+left
    assert len(K)==q and all(form(v,w)==0 for v in K for w in K)
    return 2*r

def exact_profiles():
    for p in [2,3,5,7]:
        for m in [1,2,3]:
            n=2*m
            V=[tuple(int(i==j) for i in range(n)) for j in range(n)]
            probes=[V]
            if p!=2:
                probes+=[[scale(2,v,p) if i<2*h and i%2==0 else v
                          for i,v in enumerate(V)] for h in range(1,m+1)]
            if m>=2:
                probes+=[[add(v,V[2],p) if i==0 else v for i,v in enumerate(V)]]
            probes+=[[add(v,V[j],p) if i==j+1 else v for i,v in enumerate(V)]
                     for j in range(n-1)]
            defects=[realization(p,m,b) for b in probes]
            assert defects[0]==0
            if p!=2: assert defects[1:m+1]==list(range(2,n+1,2))
            if m>=2: assert defects[1+(m if p!=2 else 0)]==2
            print("exact realization p=%d m=%d profiles=%d ranks=%s" %
                  (p,m,len(defects),','.join(map(str,sorted(set(defects))))))

if __name__=='__main__':
    source()
    exact_profiles()
    print("PASS exact modular-label checker")
