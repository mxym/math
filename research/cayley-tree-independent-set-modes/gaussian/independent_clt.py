"""Independent exact finite sanity checks supplementing a mathematical CLT proof.
No author imports; run under python -B -O. Computer enumeration is not a test of
normality at finite orders and is not a substitute for a limit theorem."""
from fractions import Fraction as F
from itertools import permutations,product
from math import factorial
from collections import Counter,defaultdict
def need(s):
    if not s:raise ArithmeticError('exact test failed')
def graph(T):
    adj=[]
    def add(t,par):
        u=len(adj);adj.append(set())
        if par is not None: adj[u].add(par);adj[par].add(u)
        for w in t:add(w,u)
    add(T,None);return adj
def distances(g,s):
    d={s:0};order=[s]
    for v in order:
        for w in g[v]:
            if w not in d:d[w]=d[v]+1;order.append(w)
    return d
def labeled_masks(g):
    E=[(1<<i)|(1<<j) for i in range(len(g)) for j in g[i] if i<j]
    return [m for m in range(1<<len(g)) if not any((m&e)==e for e in E)]
def root_aut(g):
    d=distances(g,0);parts=defaultdict(list)
    for v in range(len(g)):parts[d[v],len(g[v])].append(v)
    blocks=list(parts.values()); ordered=sum(blocks,[]); found=0
    for p in product(*(permutations(b) for b in blocks)):
        pi=dict(zip(ordered,sum((list(b) for b in p),[])))
        if all({pi[j] for j in g[i]}==g[pi[i]] for i in range(len(g))):found+=1
    return found
leaf=(); length2=(leaf,);length3=(length2,)
S=(leaf,(leaf,leaf),(leaf,length3))
R=(length2,length2,(length2,length2))
def new_rooted(T):
    yield tuple(sorted((*T,())))
    for i,c in enumerate(T):
        for cc in new_rooted(c):yield tuple(sorted((*T[:i],cc,*T[i+1:])))
def generations(n):
    prev={()}
    yield prev
    for k in range(2,n+1):
        prev={u for T in prev for u in new_rooted(T)}
        yield prev
def host_tests():
    tab=[]
    for x in (S,R):
        g=graph(x);need(len(g)==10)
        masks=labeled_masks(g)
        stats=tuple((sum((m&1)==v for m in masks),sum((m.bit_count()) for m in masks if m&1==v)) for v in (0,1))
        tab.append(stats)
    need(tab==[((130,395),(40,140)),((117,336),(36,120))])
    A=[root_aut(graph(t)) for t in (S,R)];need(A==[2,4])
    p=F(1,A[0])/(F(1,A[0])+F(1,A[1]))
    # Exact primal transfer: exterior states are enumerated in every small host
    # tree. If a vertex joined to the gadget is occupied the slot is root-out
    # only; otherwise the slot may have either root-bit. Host may have two distinct
    # attached slots with independent choices; test a SECOND swap in either filling.
    def value(ext,w,slots,gadgets):
        z=s=0
        for bits in ext:
            states=[tab[i][0] if bits&(1<<v) else
                (tab[i][0][0]+tab[i][1][0],tab[i][0][1]+tab[i][1][1]) for v,i in zip(slots,gadgets)]
            wt=1
            for u,j in states:wt*=u
            z+=wt;s+=wt*bits.bit_count()+sum((wt//u)*j for u,j in states)
        return F(s,z),z
    cases=0
    for row in generations(7):
        for t in row:
            g=graph(t); masks=labeled_masks(g)
            for i in range(len(g)):
                for j in range(i,len(g)):
                    vals=[value(masks,None,(i,j),u) for u in ((1,1),(0,1),(1,0),(0,0))]
                    m,z=vals[0]
                    for (y,b),cnt in zip(vals,(0,1,1,2)):
                        need(y-m==F(cnt,6) and F(b,z)==F(10,9)**cnt)
                    cases+=1
    c=(F(1,A[0])+F(1,A[1]))*p*(1-p)/36
    need(c==F(1,216))
    print('Root-in/out jet pairs by subset enumeration:',tab,'automorphisms by explicit permutations:',A)
    print('All two-gadget rooted host/attachment pairs, exterior size ≤7:',cases,'exact mass factors and mean shifts. e^-10 variance coefficient:',c)
def anchoring():
    shapes=cuts=balls=0;global_sizes=[]
    for row in generations(9):
        global_sizes.append(len(row))
        for t in row:
            shapes+=1;g=graph(t);n=len(g); D=[distances(g,v) for v in range(n)]
            anc=[[a for a in range(n) if D[0][a]+D[v][a]==D[0][v]] for v in range(n)]
            for h in range(1,5):
                masks=[{w for w in range(n) if D[v][w]<=h} for v in range(n)]
                for K in (2,3,5,8,10):
                    valid=touch=0
                    for a in range(n):
                        eligible=0
                        for v in range(n):
                            if a not in anc[v] or D[v][a]!=h:continue
                            fringe={w for w in range(n) if a in anc[w]}
                            # count each vertex at a single anchor; re-compute distances
                            # in the cut graph to check absence of an invisible shortcut.
                            local={u:(g[u]&fringe) for u in fringe}
                            here={w for w,d in distances(local,v).items() if d<=h}
                            need(here==masks[v])
                            if len(here)<=K:eligible+=1
                            balls+=1
                        # True degree here equals root's child count plus possibly one
                        # parent edge; subtract that edge when we move to its fringe tree.
                        need(eligible<=(len(g[a])-int(a!=0))*K**(h-1))
                        valid+=eligible
                    miss=sum(1 for v in range(n) if D[0][v]<h and len(masks[v])<=K)
                    need(valid+miss==sum(len(s)<=K for s in masks));cuts+=1
    need(global_sizes==[1,1,2,4,9,20,48,115,286])
    print('Exhausted rooted nonplane shapes (n=1..9):',global_sizes,'total',shapes)
    print('Anchor identity/degree-bound checks (shape,h,K):',cuts,'full vs descendant ball vertex comparisons:',balls)
if __name__=='__main__':
    host_tests();anchoring();print('PASS')
