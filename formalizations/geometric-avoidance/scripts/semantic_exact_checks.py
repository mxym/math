#!/usr/bin/env python3
"""Independent finite regressions, using exact integer/rational arithmetic only.
These supplement the source/Lean audit; they do not replace universal proofs.
"""
from fractions import Fraction as F
from itertools import product
from math import ceil, floor, prod
from collections import Counter
import json

counts = Counter()
def check(value, name):
    if not value:
        raise RuntimeError('FAILED: ' + name)
    counts[name] += 1

def span(M,g,L,h):
    if h == 0: return 0
    return M*(L if h == 1 else 2*(g+span(M,g,L,h-1)))+(M-1)*g

def length(M,g,L,h): return L if h<=1 else g+span(M,g,L,h-1)
def block(M,g,L,h): return L if h<=1 else 2*(g+span(M,g,L,h-1))
def tree(M,g,L,d,U):
    edges=[]
    def rec(h,u,path):
        if not h: return
        for i in range(M):
            a=u+i*(block(M,g,L,h)+g)
            e=(path+(i,),a,length(M,g,L,h),a+length(M,g,L,h)-1,a+block(M,g,L,h)-1)
            edges.append(e)
            rec(h-1,a+length(M,g,L,h)+g,path+(i,))
    rec(d,U,())
    return edges

# Compare actual recursively positioned tree with an independent sequential
# preorder schedule, across children that are selectors and defaults alike.
for M,d,g,L in product(range(1,5),range(1,5),(0,1,3,8),(1,2,7)):
    U=g+5
    E=tree(M,g,L,d,U)
    cursor=U
    for e in E:
        path,a,ell,b,star=e
        check(a==cursor,'preorder_exact_positions')
        cursor=b+g+1
        check(star+1<=a+2*ell,'subtree_local_span')
        check(ell>=L,'local_length_at_least_base')
    check(cursor-g==U+span(M,g,L,d),'total_span_exact')
    for idx,e in enumerate(E):
        path,a,ell,b,star=e
        for f in E[:idx]:
            check(f[3]+g+1<=a,'all_earlier_predecessor_bounds')
        for f in E:
            if f[0][:len(path)]==path:
                check(b<=f[3]<=star,'all_descendant_grid_bounds')

# Finite exact joint laws. Terminals may depend on every selector, including
# shared auxiliaries and false own bits. All permutations of terminal indices
# are permitted; this tests the crucial conditioning order independently.
S,T,m=5,3,2
for p in (F(0),F(1,7),F(1,2),F(1)):
    for exposed_bit in (0,1):
        for mode in range(4):
            total=F(0)
            for sig in product((0,1),repeat=S):
                # Coordinate 0 is exposed; 1,2 are distinct free own bits.
                shift=(sum(sig) if mode==0 else sig[1]+2*sig[2]+sig[3]*sig[4])%T
                terms=[(shift+i)%T for i in range(m)]
                if mode in (2,3): terms.reverse()
                for tau in product((0,1),repeat=T):
                    w=F(1,2)**S*prod(p if b else 1-p for b in tau)
                    event=sig[0]==exposed_bit and all(not(sig[i+1] and tau[terms[i]]) for i in range(m))
                    if event: total+=w
            check(total==F(1,2)*(1-p/2)**m,'joint_selector_dependent_terminal_law')

# Three counterexamples prove that dropping any contract hypothesis really
# changes the law. These are numerical witnesses, not altered Lean sources.
def miss(own,terminal,exposed,p=F(1,2),S=3,T=2):
    value=F(0); atom=F(0)
    for sig in product((0,1),repeat=S):
        for tau in product((0,1),repeat=T):
            w=F(1,2)**S*prod(p if b else 1-p for b in tau)
            if all(sig[i]==b for i,b in exposed.items()):
                atom+=w
                if all(not(sig[o] and tau[t]) for o,t in zip(own,terminal(sig))): value+=w
    return value,atom*(1-p/2)**len(own)
for name,args in (
 ('duplicate_own_detected',([1,1],lambda s:[0,1],{})),
 ('exposed_own_detected',([0,1],lambda s:[0,1],{0:0})),
 ('duplicate_terminal_detected',([1,2],lambda s:[0,0],{})),
):
    a,b=miss(*args)
    check(a!=b,name)

# Actual active points, key separation, original-index guards, and predecessor
# stability use rational s, t and exact powers. No floating logarithm is used.
def dyadic(e): return F(2**e) if e>=0 else F(1,2**(-e))
def key(b,z):
    N=2**(b+3)
    return floor(N*z)%N
for M,d,g,L,U in ((2,2,8,32,30),(3,2,10,32,32),(2,3,12,32,34)):
    E=tree(M,g,L,d,U); bypath={e[0]:e for e in E}
    selectors=[e for e in E if e[0][-1]<M-1]
    def route(z,selector,prefix=()):
        path=prefix
        while len(path)<d:
            child=next((i for i in range(M-1) if selector(path+(i,),key(bypath[path+(i,)][3],z))),M-1)
            path=path+(child,)
        return path
    for s,t,k,x in product((F(1,2),F(1),F(3,2),F(2)),(F(1),F(3,2),F(2)),(-7,0,5),(F(-3,7),F(0),F(2,7),F(1),F(9,7))):
        stride=8; Ntail=3
        budget=ceil(F(U+span(M,g,L,d)+abs(k),3))+1
        stable=all(floor(2**(a-g+2)*(x+dyadic(-(a-1))))==floor(2**(a-g+2)*x) for _,a,_,_,_ in E)
        for v in sorted({e[0][:-1] for e in selectors}):
            pairs=[]
            for e in selectors:
                path,a,ell,b,star=e
                if path[:-1]!=v: continue
                for label in range(budget):
                    j=stride*label
                    if a<s*j-k<a+ell:
                        check(j>=Ntail,'original_tail_guard')
                        offset=t*dyadic(int(k-s*j)); z=x+offset
                        check(key(b,z)!=key(b,x),'own_address_unexposed')
                        pairs.append((e,j,z))
                        if stable:
                            for f in selectors:
                                if f[1]<a: check(key(f[3],z)==key(f[3],x),'stable_all_preceding_keys')
            own=[(e[0],key(e[3],z)) for e,j,z in pairs]
            check(len(own)==len(set(own)),'actual_own_addresses_injective')
            for mode in range(4):
                def selector(path,q):
                    if mode==0: return False
                    if mode==1: return True
                    return bool((q+sum((i+1)*(v+1) for i,v in enumerate(path))+mode)%3)
                terms=[]
                for e,j,z in pairs:
                    path=route(z,selector,e[0]); terms.append((path,key(bypath[path][3],z)))
                    # Compare readout at point with canonical left endpoint of
                    # its finest local cell; both selector and terminal addresses.
                    star=e[4]; left=F(key(star,z),2**(star+3))
                    path_left=route(left,selector,e[0])
                    check(path_left==path and key(bypath[path][3],left)==key(bypath[path][3],z),'local_readout_finest_key_factorization')
                check(len(terms)==len(set(terms)),'actual_terminal_addresses_injective')
        if stable:
            for seed in range(3):
                def selector(path,q):
                    if q==key(bypath[path][3],x): return False
                    return bool((q+seed+sum(path))%3)
                center_route=route(x,selector)
                for e in selectors:
                    path,a,ell,b,star=e
                    if center_route[:len(path)-1]!=path[:-1]: continue
                    for label in range(budget):
                        j=stride*label
                        if a<s*j-k<a+ell:
                            z=x+t*dyadic(int(k-s*j))
                            if selector(path,key(b,z)):
                                check(route(z,selector)==route(z,selector,path),'local_success_routes_globally')

# Empty candidate family must retain the arrangement constant (500).
for ell in range(8):
    for P in (0,1,2,7):
        lhs=20*(P*(3+2**(2*ell+3))+5)**2
        rhs=5120*(P+1)**2*2**(4*ell)
        check(lhs<=rhs,'entropy_constant_retained')
check(20*(0*(3+2**3)+5)**2==500,'zero_candidates_cost_500')
# Original-index counting at strict endpoints and signed coefficient scales.
for s,u,ell,k,N in product((F(1,2),F(1),F(3,2),F(2)),(20,23,29),(32,37,48),(-7,0,5),(0,3)):
    m=8; upper_s=2; T=ell+7; U=u
    budget=ceil(F(U+T+abs(k),3))+1
    labels=[n for n in range(budget) if u<s*m*n-k<u+ell]
    independently=[n for n in range(ceil(F(u+ell+k,1)/(s*m))+2) if u<s*m*n-k<u+ell]
    check(labels==independently,'candidate_budget_complete')
    check(F(ell,2*m*upper_s)<=len(labels)<=1+F(ell,3),'strict_active_count_bounds')
    check(all(m*n>=N for n in labels),'counted_original_tail')
    check(all(not(u<s*m*n-k<u+ell) for n in range(budget) if s*m*n-k in (u,u+ell)),'strict_endpoints_excluded')

# Enumerate exact actual no-default routes through full finite ordered trees.
for M,d in product((2,3),(1,2)):
    edges=[prefix+(child,) for depth in range(d) for prefix in product(range(M),repeat=depth) for child in range(M-1)]
    surviving=0
    for vals in product((0,1),repeat=len(edges)):
        bits=dict(zip(edges,vals)); path=(); ok=True
        for level in range(d):
            chosen=next((i for i in range(M-1) if bits[path+(i,)]),M-1)
            ok=ok and chosen<M-1; path=path+(chosen,)
        surviving+=int(ok)
    check(F(surviving,2**len(edges))==(1-F(1,2)**(M-1))**d,'actual_no_default_law')

def merged_length(intervals):
    intervals=sorted((max(F(0),a),min(F(1),b)) for a,b in intervals if max(F(0),a)<min(F(1),b))
    total=F(0); current=None
    for a,b in intervals:
        if current is None: current=[a,b]
        elif a<=current[1]: current[1]=max(current[1],b)
        else: total+=current[1]-current[0]; current=[a,b]
    if current is not None: total+=current[1]-current[0]
    return total
for N in (1,2,4,8):
    for mask in range(2**N):
        cells=[j for j in range(N) if mask>>j&1]
        for p in (F(1,7),F(1,2),F(1)):
            r=p/(8*N)
            intervals=[(F(j,N)+k-2*r,F(j+1,N)+k+2*r) for j in cells for k in (-1,0,1)]
            density=merged_length(intervals)
            check(density<=F(len(cells),N)+4*N*r,'periodic_double_buffer_wrap_budget')
            check(4*N*r==p/2<p,'positive_buffer_exact_cost')
print(json.dumps({'status':'PASS','arithmetic':'exact integers and fractions','counts':dict(sorted(counts.items())),'total_checks':sum(counts.values()),'scope':'Finite regression evidence only; universal statements require Lean/source proof audit.'},sort_keys=True,indent=2))
